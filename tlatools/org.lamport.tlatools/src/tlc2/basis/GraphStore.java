/*******************************************************************************
 * Copyright (c) 2026 Basis Research Institute. All rights reserved.
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ******************************************************************************/
package tlc2.basis;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.LongAdder;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.util.BitVector;
import tlc2.util.Context;
import tlc2.util.IStateWriter;
import tlc2.util.LongVec;
import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;

/**
 * What TLC computes and throws away, kept: every reached state's content,
 * how it was first reached, its predecessors, and the guard conjuncts that
 * kept transitions from firing.
 *
 * <p>
 * TLC itself stores only fingerprints ({@code FPSet}) and one parent pointer
 * per state ({@code TLCTrace}); reconstructing a state means re-running the
 * next-state relation from an initial state. This store sits on the
 * {@link IStateWriter} hook the checker already calls on every edge
 * ({@code ModelChecker.isSeenState}, {@code Worker.addElement}) and on every
 * guard that evaluated false ({@code Worker.addUnsatisfiedState}, routed here
 * because {@link #isConstrained()} is true), so the checker core is
 * untouched.
 *
 * <p>
 * State content goes to one append-only file under the metadir, serialised
 * the way {@code DiskStateQueue} serialises states; the index (fingerprint
 * to offset, level and first predecessor) and the predecessor lists stay in
 * memory. Successors a constraint excluded are kept as well, content and
 * edge, since TLC checks invariants on them and an invariant sweep must too.
 * Blocked guards are tallied, not logged: per (action, conjunct)
 * a count, one example state and one example binding. The tallies take no
 * lock (a false guard is reported far more often than an edge); edges and
 * states are recorded under the store's lock, which costs a run with many
 * edges per state noticeable time (about 1.4x on a spec with 3.4M edges,
 * one worker or four).
 *
 * <p>
 * The in-memory part is not bounded: roughly a hundred bytes of heap per
 * state and fifty per edge, on top of the checker's own. It suits the specs
 * one iterates on interactively; for a large run, open the resident with
 * {@code store: false} (no store, no store queries) or give the JVM the heap.
 */
public final class GraphStore implements IStateWriter {

	/** How a state was first reached, and where its content is. */
	private static final class Entry {
		final long offset;
		final int length;
		final int level;
		/** Fingerprint of the state this one was first reached from, or 0 for an initial state. */
		final long predecessor;
		/** The action that first reached it, or -1. */
		final int action;

		Entry(long offset, int length, int level, long predecessor, int action) {
			this.offset = offset;
			this.length = length;
			this.level = level;
			this.predecessor = predecessor;
			this.action = action;
		}
	}

	/** One guard conjunct's (or constraint's) tally of the transitions it disabled. */
	public static final class Blocked {
		public final int actionId;
		public final String action;
		/** {@code guard}: a conjunct of the action evaluated false; {@code constraint}: a state or action constraint excluded the successor. */
		public final String kind;
		public final String location;
		public final String text;
		/** The count when this row was read ({@link GraphStore#blocked()} returns snapshots). */
		public long count;
		public long exampleFp;
		public Map<String, String> exampleBindings;
		private final LongAdder tally = new LongAdder();

		Blocked(int actionId, String action, String kind, String location, String text) {
			this.actionId = actionId;
			this.action = action;
			this.kind = kind;
			this.location = location;
			this.text = text;
		}

		private Blocked snapshot() {
			final Blocked b = new Blocked(actionId, action, kind, location, text);
			b.count = tally.sum();
			b.exampleFp = exampleFp;
			b.exampleBindings = exampleBindings;
			return b;
		}
	}

	/**
	 * What a tally is kept per: the action, the conjunct's node (by identity:
	 * it is the same node on every evaluation, so no text or location is
	 * built on the hot path) and whether it is a guard or a constraint.
	 */
	private static final class TallyKey {
		final int actionId;
		final SemanticNode pred;
		final boolean constraint;

		TallyKey(int actionId, SemanticNode pred, boolean constraint) {
			this.actionId = actionId;
			this.pred = pred;
			this.constraint = constraint;
		}

		@Override
		public boolean equals(final Object o) {
			if (!(o instanceof TallyKey)) {
				return false;
			}
			final TallyKey k = (TallyKey) o;
			return actionId == k.actionId && pred == k.pred && constraint == k.constraint;
		}

		@Override
		public int hashCode() {
			return 31 * (31 * actionId + System.identityHashCode(pred)) + (constraint ? 1 : 0);
		}
	}

	private final File file;
	private final RandomAccessFile content;
	private final Map<Long, Entry> index = new HashMap<>();
	/**
	 * Successors a state or action constraint excluded, by fingerprint: they
	 * are not in the model and never expanded, but TLC checks every invariant
	 * on them, so their content is kept for the invariant sweeps.
	 */
	private final Map<Long, Entry> excludedIndex = new HashMap<>();
	/** Fingerprint to (excluded successor fp, action id) pairs, each edge once. */
	private final Map<Long, LongVec> excludedEdges = new HashMap<>();
	/** Fingerprint to (predecessor fp, action id, flags) triples. */
	private final Map<Long, LongVec> predecessors = new HashMap<>();
	private final Map<Integer, Action> actions = new HashMap<>();
	/**
	 * Tallied without the store's lock: every worker reports every false
	 * guard, many times more often than it reports an edge.
	 */
	private final ConcurrentHashMap<TallyKey, Blocked> blocked = new ConcurrentHashMap<>();
	private final List<Long> initial = new ArrayList<>();
	/**
	 * Initial states a state constraint excluded, kept in
	 * {@link #excludedIndex}: TLC checks invariants and state-level
	 * properties on them too.
	 */
	private final java.util.Set<Long> excludedInitial = new java.util.LinkedHashSet<>();
	private long edges;
	private final LongAdder unsatisfied = new LongAdder();
	private final LongAdder excluded = new LongAdder();
	private TLCState empty;
	/** Serialised states not yet written to {@link #content}; flushed before a read. */
	private final ByteArrayOutputStream pending = new ByteArrayOutputStream(1 << 16);
	/** Bytes in {@link #content} plus {@link #pending}: the next state's offset. */
	private long length;
	private static final int FLUSH_AT = 1 << 20;

	public GraphStore(final String metadir) throws IOException {
		this.file = new File(metadir, "basis.states");
		this.content = new RandomAccessFile(this.file, "rw");
		this.content.setLength(0);
	}

	/** The state every stored one is read into a copy of. */
	private TLCState empty() {
		if (empty == null) {
			empty = TLCState.Empty.createEmpty();
		}
		return empty;
	}

	// ─── what the checker writes ────────────────────────────────────────

	@Override
	public void writeState(final TLCState state) {
		// An initial state.
		final long fp = state.fingerPrint();
		final byte[] data = serialise(state);
		synchronized (this) {
			if (!index.containsKey(fp)) {
				store(fp, data, 1, 0, -1);
				initial.add(fp);
			}
		}
	}

	@Override
	public void writeExcludedInitial(final TLCState state) {
		final long fp = state.fingerPrint();
		final byte[] data = serialise(state);
		synchronized (this) {
			if (!excludedIndex.containsKey(fp)) {
				excludedIndex.put(fp, new Entry(append(data), data.length, 1, 0, -1));
			}
			excludedInitial.add(fp);
		}
	}

	@Override
	public synchronized void writeState(final TLCState state, final TLCState successor, final short stateFlags) {
		writeState(state, successor, stateFlags, (Action) null);
	}

	@Override
	public void writeState(final TLCState state, final TLCState successor, final short stateFlags,
			final Action action) {
		if (isSet(stateFlags, IsNotInModel)) {
			return;
		}
		// Fingerprinting and serialising run outside the lock: every worker
		// writes every edge here, so the lock covers only the maps.
		final long from = state.fingerPrint();
		final long to = successor.fingerPrint();
		final int actionId = action == null ? -1 : action.getId();
		// Keep the content of the write that won TLC's fingerprint-set put
		// (IsUnseen): that is the state TLC enqueued and whose successors the
		// store records. Under a VIEW or SYMMETRY another worker may reach the
		// same fingerprint with a different concrete state, and its (IsSeen)
		// write can take this lock first.
		final byte[] data = isSet(stateFlags, IsUnseen) ? serialise(successor) : null;
		synchronized (this) {
			if (action != null) {
				actions.putIfAbsent(actionId, action);
			}
			edges++;
			if (data != null && !index.containsKey(to)) {
				final Entry pred = index.get(from);
				store(to, data, pred == null ? 2 : pred.level + 1, from, actionId);
			}
			final LongVec preds = predecessors.computeIfAbsent(to, k -> new LongVec(4));
			preds.addElement(from);
			preds.addElement(actionId);
			preds.addElement(stateFlags);
		}
	}

	/**
	 * A state or action constraint {@code pred} excluded {@code successor}:
	 * the worker calls this only for constraints. Tallied apart from the
	 * guards, since the successor was generated and then dropped.
	 */
	@Override
	public void writeState(final TLCState state, final TLCState successor, final short stateFlags,
			final Action action, final SemanticNode pred) {
		excluded.increment();
		tally(state, action, pred, null, true);
		writeExcluded(state, successor, action);
	}

	/**
	 * Keep {@code successor}, which a constraint excluded when {@code action}
	 * generated it from {@code state}: its content (once per fingerprint) and
	 * the edge (once per source and action). The worker reports an excluded
	 * successor once per constraint it fails; the repeats add nothing.
	 */
	public void writeExcluded(final TLCState state, final TLCState successor, final Action action) {
		final long from = state.fingerPrint();
		final long to = successor.fingerPrint();
		final int actionId = action == null ? -1 : action.getId();
		final boolean known;
		synchronized (this) {
			known = excludedIndex.containsKey(to);
			if (known && hasExcludedEdge(from, to, actionId)) {
				return;
			}
		}
		final byte[] data = known ? null : serialise(successor);
		synchronized (this) {
			if (action != null) {
				actions.putIfAbsent(actionId, action);
			}
			if (data != null && !excludedIndex.containsKey(to)) {
				final Entry pred = index.get(from);
				excludedIndex.put(to, new Entry(append(data), data.length, pred == null ? 2 : pred.level + 1, from,
						actionId));
			}
			if (!hasExcludedEdge(from, to, actionId)) {
				final LongVec edges = excludedEdges.computeIfAbsent(from, k -> new LongVec(2));
				edges.addElement(to);
				edges.addElement(actionId);
			}
		}
	}

	/** Caller holds the lock. */
	private boolean hasExcludedEdge(final long from, final long to, final int actionId) {
		final LongVec edges = excludedEdges.get(from);
		if (edges == null) {
			return false;
		}
		for (int i = 0; i < edges.size(); i += 2) {
			if (edges.elementAt(i) == to && edges.elementAt(i + 1) == actionId) {
				return true;
			}
		}
		return false;
	}

	/**
	 * A guard conjunct evaluated false: the transition {@code action} was not
	 * enabled at {@code state} because of {@code pred}, under the quantifier
	 * bindings in {@code c}. Tallied per (action, conjunct).
	 */
	@Override
	public void writeUnsatisfied(final TLCState state, final Action action, final TLCState successor,
			final SemanticNode pred, final Context c) {
		unsatisfied.increment();
		tally(state, action, pred, c, false);
	}

	private void tally(final TLCState state, final Action action, final SemanticNode pred, final Context c,
			final boolean constraint) {
		final int actionId = action == null ? -1 : action.getId();
		final TallyKey key = new TallyKey(actionId, pred, constraint);
		Blocked b = blocked.get(key);
		if (b == null) {
			// The row's text, location and example are built once, by
			// whichever worker reports the conjunct first.
			b = blocked.computeIfAbsent(key, k -> {
				final Blocked n = new Blocked(actionId, action == null ? "?" : action.getNameOfDefault(),
						constraint ? "constraint" : "guard", pred == null ? "?" : String.valueOf(pred.getLocation()),
						text(pred));
				try {
					n.exampleFp = state.fingerPrint();
				} catch (final RuntimeException e) {
					n.exampleFp = 0;
				}
				if (c != null) {
					final Map<String, String> bindings = new HashMap<>();
					c.toMap().forEach((name, v) -> bindings.put(name.toString(), v.toString()));
					n.exampleBindings = bindings;
				}
				return n;
			});
		}
		b.tally.increment();
	}

	/** The source text of a semantic node, or its location when the parse tree is gone. */
	public static String text(final SemanticNode node) {
		if (node == null) {
			return "";
		}
		if (node.getTreeNode() instanceof SyntaxTreeNode) {
			return ((SyntaxTreeNode) node.getTreeNode()).getHumanReadableImage();
		}
		return String.valueOf(node.getLocation());
	}

	@Override
	public void writeState(final TLCState state, final TLCState successor, final short stateFlags,
			final Visualization visualization) {
		// Stuttering steps carry no new state.
	}

	@Override
	public void writeState(final TLCState state, final TLCState successor, final BitVector actionChecks,
			final int from, final int length, final short stateFlags) {
		writeState(state, successor, stateFlags, (Action) null);
	}

	@Override
	public void writeState(final TLCState state, final TLCState successor, final BitVector actionChecks,
			final int from, final int length, final short stateFlags, final Visualization visualization) {
		writeState(state, successor, stateFlags, (Action) null);
	}

	/**
	 * The checker closes its state writer when a run ends; the store outlives
	 * the run, so this only flushes. {@link #dispose()} releases it.
	 */
	@Override
	public synchronized void close() {
		try {
			flush();
			content.getFD().sync();
		} catch (final IOException e) {
			// Nothing to report to.
		}
	}

	/**
	 * Release the store for good: close its file, delete it, and delete its
	 * directory when nothing else is left in it (a refresh's own metadir; the
	 * checker's metadir holds TLC's files too and stays).
	 */
	public synchronized void dispose() {
		try {
			content.close();
		} catch (final IOException e) {
			// Deleting below is what matters.
		}
		pending.reset();
		delete(file);
		final File dir = file.getParentFile();
		if (dir != null) {
			final String[] left = dir.list();
			if (left != null && left.length == 0) {
				delete(dir);
			}
		}
	}

	/**
	 * Delete {@code f}, retrying briefly: on Windows another process (a virus
	 * scanner, the indexer) can hold a freshly written file open for a moment,
	 * and the delete fails until it lets go. Left to the JVM's exit otherwise.
	 */
	private static void delete(final File f) {
		for (int attempt = 0; attempt < 20; attempt++) {
			if (f.delete() || !f.exists()) {
				return;
			}
			try {
				Thread.sleep(25);
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
				break;
			}
		}
		f.deleteOnExit();
	}

	@Override
	public String getDumpFileName() {
		return file.getPath();
	}

	@Override
	public boolean isNoop() {
		return false;
	}

	@Override
	public boolean isDot() {
		return false;
	}

	/** True, so the worker routes blocked guards here. */
	@Override
	public boolean isConstrained() {
		return true;
	}

	@Override
	public synchronized void snapshot() throws IOException {
		flush();
		content.getFD().sync();
	}

	// ─── storing and reading content ────────────────────────────────────

	/**
	 * A state's variable values as bytes. Only the values: the TLCState
	 * header (worker id, uid, level) is unset on the states the writer hook
	 * receives, and the nat encodings reject negative values.
	 */
	private static byte[] serialise(final TLCState state) {
		final Serialiser ser = SERIALISER.get();
		try {
			// The stream first: resetting it flushes what it still buffers,
			// which after a write that threw part way is a partial value that
			// must not land in front of this state.
			ser.vos.reset();
			ser.bytes.reset();
			for (final tla2sany.semantic.OpDeclNode var : state.getVars()) {
				final tlc2.value.IValue value = state.lookup(var.getName());
				if (value == null) {
					throw new IOException("unassigned variable " + var.getName() + " in a stored state");
				}
				value.write(ser.vos);
			}
			ser.vos.reset();
			return ser.bytes.toByteArray();
		} catch (final IOException e) {
			throw new RuntimeException("basis.states: " + e.getMessage(), e);
		}
	}

	/**
	 * One per worker thread: a value stream costs an 8 KiB buffer to build,
	 * and every stored state is serialised on the worker that reached it.
	 */
	private static final class Serialiser {
		final ByteArrayOutputStream bytes = new ByteArrayOutputStream(256);
		final ValueOutputStream vos;

		Serialiser() {
			try {
				vos = new ValueOutputStream(bytes, false);
			} catch (final IOException e) {
				throw new RuntimeException(e);
			}
		}
	}

	private static final ThreadLocal<Serialiser> SERIALISER = ThreadLocal.withInitial(Serialiser::new);

	/** Append serialised content; the file write is batched. Caller holds the lock. */
	private void store(final long fp, final byte[] data, final int level, final long predecessor,
			final int action) {
		index.put(fp, new Entry(append(data), data.length, level, predecessor, action));
	}

	/** Append serialised content and return its offset. Caller holds the lock. */
	private long append(final byte[] data) {
		final long offset = length;
		pending.write(data, 0, data.length);
		length += data.length;
		if (pending.size() >= FLUSH_AT) {
			try {
				flush();
			} catch (final IOException e) {
				throw new RuntimeException("basis.states: " + e.getMessage(), e);
			}
		}
		return offset;
	}

	/** A state in the model, else an excluded successor, else null. Caller holds the lock. */
	private Entry entry(final long fp) {
		final Entry e = index.get(fp);
		return e != null ? e : excludedIndex.get(fp);
	}

	private void flush() throws IOException {
		if (pending.size() == 0) {
			return;
		}
		content.seek(content.length());
		pending.writeTo(new java.io.OutputStream() {
			@Override
			public void write(final int b) throws IOException {
				content.write(b);
			}

			@Override
			public void write(final byte[] b, final int off, final int len) throws IOException {
				content.write(b, off, len);
			}
		});
		pending.reset();
	}

	/** The stored state (in the model, or an excluded successor) with this fingerprint, or null. */
	public synchronized TLCState read(final long fp) {
		final Entry e = entry(fp);
		if (e == null) {
			return null;
		}
		try {
			flush();
			final byte[] data = new byte[e.length];
			content.seek(e.offset);
			content.readFully(data);
			final ValueInputStream vis = new ValueInputStream(new ByteArrayInputStream(data));
			TLCState state = empty().createEmpty();
			for (final tla2sany.semantic.OpDeclNode var : state.getVars()) {
				state = state.bind(var.getName(), vis.read());
			}
			vis.close();
			return state;
		} catch (final IOException e2) {
			throw new RuntimeException("basis.states: " + e2.getMessage(), e2);
		}
	}

	public synchronized boolean contains(final long fp) {
		return index.containsKey(fp);
	}

	public synchronized Integer level(final long fp) {
		final Entry e = entry(fp);
		return e == null ? null : e.level;
	}

	/** Every stored fingerprint, in no particular order. */
	public synchronized long[] fingerprints() {
		final long[] out = new long[index.size()];
		int i = 0;
		for (final Long fp : index.keySet()) {
			out[i++] = fp;
		}
		return out;
	}

	/**
	 * The fingerprints from an initial state to {@code fp} along first
	 * predecessors, with the action id taken at each step (-1 for the initial
	 * state). Null when {@code fp} is not stored.
	 */
	public synchronized long[][] pathTo(final long fp) {
		if (entry(fp) == null) {
			return null;
		}
		final List<long[]> reversed = new ArrayList<>();
		long cur = fp;
		while (true) {
			// An excluded successor ends a path; every state before it is in the model.
			final Entry e = cur == fp ? entry(cur) : index.get(cur);
			if (e == null) {
				break;
			}
			reversed.add(new long[] { cur, e.action });
			if (e.action < 0 || e.predecessor == cur) {
				break;
			}
			cur = e.predecessor;
		}
		final long[][] path = new long[reversed.size()][];
		for (int i = 0; i < path.length; i++) {
			path[i] = reversed.get(path.length - 1 - i);
		}
		return path;
	}

	/** Whether {@code fp} was kept as an excluded successor (it may also be in the model). */
	public synchronized boolean isExcluded(final long fp) {
		return excludedIndex.containsKey(fp);
	}

	/** The excluded successors not also in the model: TLC checked invariants on them, and never expanded them. */
	public synchronized long[] excludedFingerprints() {
		final List<Long> out = new ArrayList<>();
		for (final Long fp : excludedIndex.keySet()) {
			if (!index.containsKey(fp)) {
				out.add(fp);
			}
		}
		final long[] a = new long[out.size()];
		for (int i = 0; i < a.length; i++) {
			a[i] = out.get(i);
		}
		return a;
	}

	/** (excluded successor fp, action id) pairs generated from {@code fp}. */
	public synchronized long[][] excludedSuccessors(final long fp) {
		final LongVec v = excludedEdges.get(fp);
		if (v == null) {
			return new long[0][];
		}
		final long[][] out = new long[v.size() / 2][];
		for (int i = 0; i < out.length; i++) {
			out[i] = new long[] { v.elementAt(2 * i), v.elementAt(2 * i + 1) };
		}
		return out;
	}

	/** Excluded successors kept, whether or not they are also in the model. */
	public synchronized long excludedStates() {
		return excludedIndex.size();
	}

	/** (predecessor fp, action id, flags) triples recorded into {@code fp}. */
	public synchronized long[][] predecessorsOf(final long fp) {
		final LongVec v = predecessors.get(fp);
		if (v == null) {
			return new long[0][];
		}
		final long[][] out = new long[v.size() / 3][];
		for (int i = 0; i < out.length; i++) {
			out[i] = new long[] { v.elementAt(3 * i), v.elementAt(3 * i + 1), v.elementAt(3 * i + 2) };
		}
		return out;
	}

	public synchronized Action action(final int id) {
		return actions.get(id);
	}

	/** Snapshots of the tallies, guards and constraints alike. */
	public List<Blocked> blocked() {
		final List<Blocked> out = new ArrayList<>();
		for (final Blocked b : blocked.values()) {
			out.add(b.snapshot());
		}
		out.sort((a, b) -> Long.compare(b.count, a.count));
		return out;
	}

	/** The initial states' fingerprints, in the order they were written. */
	public synchronized long[] initialFingerprints() {
		final long[] out = new long[initial.size()];
		for (int i = 0; i < out.length; i++) {
			out[i] = initial.get(i);
		}
		return out;
	}

	/** The initial states a state constraint excluded, in the order they were written. */
	public synchronized long[] excludedInitialFingerprints() {
		final long[] out = new long[excludedInitial.size()];
		int i = 0;
		for (final Long fp : excludedInitial) {
			out[i++] = fp;
		}
		return out;
	}

	/** The variable names the stored states were written with, in order. */
	public synchronized String[] variableNames() {
		final TLCState e = empty();
		final tla2sany.semantic.OpDeclNode[] vars = e.getVars();
		final String[] out = new String[vars.length];
		for (int i = 0; i < vars.length; i++) {
			out[i] = vars[i].getName().toString();
		}
		return out;
	}

	public synchronized long states() {
		return index.size();
	}

	public synchronized long edges() {
		return edges;
	}

	/** Guard conjuncts that evaluated false. */
	public long unsatisfied() {
		return unsatisfied.sum();
	}

	/** Successors a state or action constraint excluded. */
	public long excluded() {
		return excluded.sum();
	}

	public synchronized long initialStates() {
		return initial.size();
	}

	public synchronized long bytes() {
		return length;
	}
}
