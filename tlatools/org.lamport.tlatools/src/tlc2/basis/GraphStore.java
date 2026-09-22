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
 * memory. Blocked guards are tallied, not logged: per (action, conjunct)
 * a count, one example state and one example binding.
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

	/** One guard conjunct's tally of the transitions it disabled. */
	public static final class Blocked {
		public final int actionId;
		public final String action;
		public final String location;
		public final String text;
		public long count;
		public long exampleFp;
		public Map<String, String> exampleBindings;

		Blocked(int actionId, String action, String location, String text) {
			this.actionId = actionId;
			this.action = action;
			this.location = location;
			this.text = text;
		}
	}

	private final File file;
	private final RandomAccessFile content;
	private final Map<Long, Entry> index = new HashMap<>();
	/** Fingerprint to (predecessor fp, action id, flags) triples. */
	private final Map<Long, LongVec> predecessors = new HashMap<>();
	private final Map<Integer, Action> actions = new HashMap<>();
	private final Map<String, Blocked> blocked = new HashMap<>();
	private final List<Long> initial = new ArrayList<>();
	private long edges;
	private long unsatisfied;
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

	@Override
	public synchronized void writeState(final TLCState state, final TLCState successor, final short stateFlags,
			final Action action, final SemanticNode pred) {
		writeUnsatisfied(state, action, successor, pred, null);
	}

	/**
	 * A guard conjunct evaluated false: the transition {@code action} was not
	 * enabled at {@code state} because of {@code pred}, under the quantifier
	 * bindings in {@code c}. Tallied per (action, conjunct).
	 */
	public synchronized void writeUnsatisfied(final TLCState state, final Action action, final TLCState successor,
			final SemanticNode pred, final Context c) {
		unsatisfied++;
		final int actionId = action == null ? -1 : action.getId();
		final String location = pred == null ? "?" : String.valueOf(pred.getLocation());
		final String key = actionId + "|" + location;
		Blocked b = blocked.get(key);
		if (b == null) {
			b = new Blocked(actionId, action == null ? "?" : action.getNameOfDefault(), location, text(pred));
			try {
				b.exampleFp = state.fingerPrint();
			} catch (final RuntimeException e) {
				b.exampleFp = 0;
			}
			if (c != null) {
				final Map<String, String> bindings = new HashMap<>();
				c.toMap().forEach((k, v) -> bindings.put(k.toString(), v.toString()));
				b.exampleBindings = bindings;
			}
			blocked.put(key, b);
		}
		b.count++;
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
		file.delete();
		final File dir = file.getParentFile();
		if (dir != null) {
			final String[] left = dir.list();
			if (left != null && left.length == 0) {
				dir.delete();
			}
		}
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
			ser.bytes.reset();
			ser.vos.reset();
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
		final long offset = length;
		pending.write(data, 0, data.length);
		length += data.length;
		index.put(fp, new Entry(offset, data.length, level, predecessor, action));
		if (pending.size() >= FLUSH_AT) {
			try {
				flush();
			} catch (final IOException e) {
				throw new RuntimeException("basis.states: " + e.getMessage(), e);
			}
		}
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

	/** The stored state with this fingerprint, or null. */
	public synchronized TLCState read(final long fp) {
		final Entry e = index.get(fp);
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
		final Entry e = index.get(fp);
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
		if (!index.containsKey(fp)) {
			return null;
		}
		final List<long[]> reversed = new ArrayList<>();
		long cur = fp;
		while (true) {
			final Entry e = index.get(cur);
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

	public synchronized List<Blocked> blocked() {
		final List<Blocked> out = new ArrayList<>(blocked.values());
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

	public synchronized long unsatisfied() {
		return unsatisfied;
	}

	public synchronized long initialStates() {
		return initial.size();
	}

	public synchronized long bytes() {
		return length;
	}
}
