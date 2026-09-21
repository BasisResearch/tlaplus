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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import tla2sany.semantic.OpDefNode;
import tlc2.tool.Action;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Vect;

/**
 * Re-explore after a spec edit, doing only the work the edit requires.
 *
 * <p>
 * The edited spec is parsed into a new {@link Tool}. Actions and invariants
 * are paired with the old ones by name and compared by source text, and an
 * action or invariant also counts as changed when any changed operator
 * definition of the root module is named in its text (a conservative
 * approximation of "depends on"). If the variables, the initial predicate or
 * the model config changed, nothing can be reused and the caller runs a
 * fresh exploration instead.
 *
 * <p>
 * Otherwise the old store's graph is replayed: the states reachable from the
 * initial states along edges of unchanged actions survive, each copied into
 * a new store with those edges; surviving states are re-expanded under the
 * changed and added actions only; states reached for the first time are
 * expanded under every action. Every new state is checked against every
 * invariant, and every surviving state against the changed invariants.
 * Successor generation, constraints and invariant evaluation all go through
 * the new {@link Tool}, so the store is a cache of TLC's own answers, never
 * an oracle of its own.
 *
 * <p>
 * Not covered here: liveness (the tableau is not rebuilt), deadlock
 * reporting, and the blocked-guard tallies for the re-expanded states
 * (successor generation here does not pass through the constrained writer).
 */
public final class Incremental {

	/** How an old action maps to the new spec. */
	public static final class ActionDiff {
		public final List<String> unchanged = new ArrayList<>();
		public final List<String> changed = new ArrayList<>();
		public final List<String> added = new ArrayList<>();
		public final List<String> removed = new ArrayList<>();
		/** Old action id to the new action, for unchanged actions. */
		final Map<Integer, Action> carried = new HashMap<>();
		/** New actions to re-expand surviving states under. */
		final List<Action> reexpand = new ArrayList<>();
		public final List<String> changedInvariants = new ArrayList<>();
		public final List<String> changedDefinitions = new ArrayList<>();
		public String fullRerunReason;
	}

	public static final class Violation {
		public final String invariant;
		public final long fp;
		public final int level;

		Violation(String invariant, long fp, int level) {
			this.invariant = invariant;
			this.fp = fp;
			this.level = level;
		}
	}

	public static final class Result {
		public long survivors;
		public long dropped;
		public long reexpanded;
		public long newStates;
		public long edgesCopied;
		public long edgesGenerated;
		public boolean budgetExhausted;
		public final List<Violation> violations = new ArrayList<>();
		public String error;
	}

	private Incremental() {
	}

	private static String text(final Action a) {
		return a.pred == null ? "" : GraphStore.text(a.pred);
	}

	/** Pair the old and new specs' actions, invariants and definitions. */
	public static ActionDiff diff(final Tool oldTool, final Tool newTool, final GraphStore oldStore) {
		final ActionDiff d = new ActionDiff();
		// Variables.
		final String[] oldVars = TLCState.Empty == null ? new String[0] : oldStore.variableNames();
		final List<String> newVars = new ArrayList<>();
		for (final tla2sany.semantic.OpDeclNode v : newTool.getSpecProcessor().getVariablesNodes()) {
			newVars.add(v.getName().toString());
		}
		if (!new ArrayList<>(List.of(oldVars)).equals(newVars)) {
			d.fullRerunReason = "the variables changed";
			return d;
		}
		// Definitions of the root module, by name.
		final Map<String, String> oldDefs = definitions(oldTool);
		final Map<String, String> newDefs = definitions(newTool);
		for (final Map.Entry<String, String> e : newDefs.entrySet()) {
			final String before = oldDefs.get(e.getKey());
			if (before == null || !before.equals(e.getValue())) {
				d.changedDefinitions.add(e.getKey());
			}
		}
		for (final String name : oldDefs.keySet()) {
			if (!newDefs.containsKey(name)) {
				d.changedDefinitions.add(name);
			}
		}
		// Initial predicate.
		if (!initText(oldTool).equals(initText(newTool)) || mentionsChanged(initText(newTool), d.changedDefinitions)) {
			d.fullRerunReason = "the initial predicate changed";
			return d;
		}
		// Actions.
		final Map<String, Action> oldByName = new LinkedHashMap<>();
		for (final Action a : oldTool.getActions()) {
			oldByName.put(a.getNameOfDefault() + "|" + a.getId(), a);
		}
		final Map<String, List<Action>> oldByKey = new HashMap<>();
		for (final Action a : oldTool.getActions()) {
			oldByKey.computeIfAbsent(a.getNameOfDefault(), k -> new ArrayList<>()).add(a);
		}
		final Set<Integer> matchedOld = new HashSet<>();
		for (final Action n : newTool.getActions()) {
			final String name = n.getNameOfDefault();
			final List<Action> candidates = oldByKey.getOrDefault(name, List.of());
			Action match = null;
			for (final Action o : candidates) {
				if (!matchedOld.contains(o.getId()) && text(o).equals(text(n))) {
					match = o;
					break;
				}
			}
			if (match != null && !mentionsChanged(text(n), d.changedDefinitions)) {
				matchedOld.add(match.getId());
				d.carried.put(match.getId(), n);
				d.unchanged.add(name);
			} else if (!candidates.isEmpty()) {
				// Same name, different text (or a dependency changed).
				for (final Action o : candidates) {
					if (!matchedOld.contains(o.getId())) {
						matchedOld.add(o.getId());
						break;
					}
				}
				d.changed.add(name);
				d.reexpand.add(n);
			} else {
				d.added.add(name);
				d.reexpand.add(n);
			}
		}
		for (final Action o : oldTool.getActions()) {
			if (!matchedOld.contains(o.getId())) {
				d.removed.add(o.getNameOfDefault());
			}
		}
		// Invariants.
		final Map<String, String> oldInv = new HashMap<>();
		final String[] oldNames = oldTool.getInvNames();
		final Action[] oldInvs = oldTool.getInvariants();
		for (int i = 0; i < oldInvs.length; i++) {
			oldInv.put(i < oldNames.length ? oldNames[i] : oldInvs[i].getNameOfDefault(), text(oldInvs[i]));
		}
		final String[] newNames = newTool.getInvNames();
		final Action[] newInvs = newTool.getInvariants();
		for (int i = 0; i < newInvs.length; i++) {
			final String name = i < newNames.length ? newNames[i] : newInvs[i].getNameOfDefault();
			final String t = text(newInvs[i]);
			if (!t.equals(oldInv.get(name)) || mentionsChanged(t, d.changedDefinitions)) {
				d.changedInvariants.add(name);
			}
		}
		return d;
	}

	private static Map<String, String> definitions(final Tool tool) {
		final Map<String, String> out = new HashMap<>();
		final OpDefNode[] defs = tool.getSpecProcessor().getRootModule().getOpDefs();
		if (defs == null) {
			return out;
		}
		for (final OpDefNode def : defs) {
			if (def.getBody() == null) {
				continue;
			}
			out.put(def.getName().toString(), GraphStore.text(def.getBody()));
		}
		return out;
	}

	private static String initText(final Tool tool) {
		final StringBuilder sb = new StringBuilder();
		final Vect<Action> init = tool.getInitStateSpec();
		for (int i = 0; i < init.size(); i++) {
			sb.append(text(init.elementAt(i))).append('\n');
		}
		return sb.toString();
	}

	/** Whether {@code text} names any of the changed definitions (a conservative dependency test). */
	private static boolean mentionsChanged(final String text, final List<String> changed) {
		for (final String name : changed) {
			int at = text.indexOf(name);
			while (at >= 0) {
				final boolean before = at == 0 || !Character.isLetterOrDigit(text.charAt(at - 1)) && text.charAt(at - 1) != '_';
				final int end = at + name.length();
				final boolean after = end >= text.length()
						|| !Character.isLetterOrDigit(text.charAt(end)) && text.charAt(end) != '_';
				if (before && after) {
					return true;
				}
				at = text.indexOf(name, at + 1);
			}
		}
		return false;
	}

	/**
	 * Replay the old graph into {@code newStore} under {@code newTool},
	 * re-expanding only where the edit reaches. Stops at the first violation
	 * unless {@code continueOnViolation}, or when the budget runs out.
	 */
	public static Result replay(final Tool newTool, final GraphStore oldStore, final GraphStore newStore,
			final ActionDiff diff, final long budgetMs, final boolean continueOnViolation) {
		final Result r = new Result();
		final long started = System.currentTimeMillis();
		final Action[] invariants = newTool.getInvariants();
		final String[] invNames = newTool.getInvNames();
		final Set<String> changedInv = new HashSet<>(diff.changedInvariants);
		// Forward adjacency of the old graph restricted to carried actions:
		// fp -> (succ fp, new action) pairs.
		final Map<Long, List<long[]>> forward = new HashMap<>();
		for (final long fp : oldStore.fingerprints()) {
			for (final long[] p : oldStore.predecessorsOf(fp)) {
				final Action carried = diff.carried.get((int) p[1]);
				if (carried == null) {
					continue;
				}
				forward.computeIfAbsent(p[0], k -> new ArrayList<>()).add(new long[] { fp, carried.getId() });
			}
		}
		final ArrayDeque<Long> queue = new ArrayDeque<>();
		final Set<Long> seen = new HashSet<>();
		// Initial states are unchanged (the init predicate is), so they seed.
		for (final long fp : oldStore.initialFingerprints()) {
			final TLCState s = oldStore.read(fp);
			if (s == null) {
				continue;
			}
			newStore.writeState(rebind(newTool, s));
			seen.add(fp);
			queue.add(fp);
		}
		final Set<Long> oldStates = new HashSet<>();
		for (final long fp : oldStore.fingerprints()) {
			oldStates.add(fp);
		}
		boolean stop = false;
		while (!queue.isEmpty() && !stop) {
			if (System.currentTimeMillis() - started > budgetMs) {
				r.budgetExhausted = true;
				break;
			}
			final long fp = queue.poll();
			final TLCState state = rebind(newTool, newStore.read(fp));
			final boolean survivor = oldStates.contains(fp);
			if (survivor) {
				r.survivors++;
				// Carried edges: copy successors and their content.
				for (final long[] e : forward.getOrDefault(fp, List.of())) {
					final long to = e[0];
					final Action a = newTool.getActions()[actionIndex(newTool, (int) e[1])];
					final TLCState succ = newStore.contains(to) ? newStore.read(to) : rebind(newTool, oldStore.read(to));
					if (succ == null) {
						continue;
					}
					final boolean unseen = !newStore.contains(to);
					newStore.writeState(state, succ, unseen ? tlc2.util.IStateWriter.IsUnseen : tlc2.util.IStateWriter.IsSeen, a);
					r.edgesCopied++;
					if (seen.add(to)) {
						queue.add(to);
					}
				}
				// Changed invariants on a survivor.
				for (int k = 0; k < invariants.length; k++) {
					final String name = k < invNames.length ? invNames[k] : invariants[k].getNameOfDefault();
					if (changedInv.contains(name) && !newTool.isValid(invariants[k], state)) {
						r.violations.add(new Violation(name, fp, newStore.level(fp)));
						if (!continueOnViolation) {
							stop = true;
							break;
						}
					}
				}
				if (stop) {
					break;
				}
				if (!diff.reexpand.isEmpty()) {
					r.reexpanded++;
				}
				stop = expand(newTool, newStore, state, fp, diff.reexpand, invariants, invNames, continueOnViolation,
						seen, queue, r);
			} else {
				r.newStates++;
				stop = expand(newTool, newStore, state, fp, List.of(newTool.getActions()), invariants, invNames,
						continueOnViolation, seen, queue, r);
			}
		}
		r.dropped = oldStates.size() - r.survivors;
		return r;
	}

	private static int actionIndex(final Tool tool, final int id) {
		final Action[] actions = tool.getActions();
		for (int i = 0; i < actions.length; i++) {
			if (actions[i].getId() == id) {
				return i;
			}
		}
		throw new IllegalStateException("no action with id " + id);
	}

	/** A stored state rebuilt against the new spec's variable set. */
	private static TLCState rebind(final Tool tool, final TLCState s) {
		if (s == null) {
			return null;
		}
		TLCState out = TLCState.Empty.createEmpty();
		for (final tla2sany.semantic.OpDeclNode v : out.getVars()) {
			final tlc2.value.IValue value = s.lookup(v.getName());
			if (value != null) {
				out = out.bind(v.getName(), value);
			}
		}
		return out;
	}

	/** Expand one state under {@code actions}; returns true to stop. */
	private static boolean expand(final Tool tool, final GraphStore store, final TLCState state, final long fp,
			final List<Action> actions, final Action[] invariants, final String[] invNames,
			final boolean continueOnViolation, final Set<Long> seen, final ArrayDeque<Long> queue, final Result r) {
		for (final Action a : actions) {
			final StateVec next;
			try {
				next = tool.getNextStates(a, state);
			} catch (final Throwable t) {
				r.error = a.getNameOfDefault() + ": " + t;
				return true;
			}
			for (int i = 0; i < next.size(); i++) {
				final TLCState succ = next.elementAt(i);
				if (!succ.allAssigned()) {
					r.error = a.getNameOfDefault() + " left " + succ.getUnassigned() + " unassigned";
					return true;
				}
				boolean inModel;
				try {
					inModel = tool.isInModel(succ) && tool.isInActions(state, succ);
				} catch (final Throwable t) {
					r.error = "constraint: " + t;
					return true;
				}
				if (!inModel) {
					continue;
				}
				final long to = succ.fingerPrint();
				final boolean unseen = !store.contains(to);
				store.writeState(state, succ, unseen ? tlc2.util.IStateWriter.IsUnseen : tlc2.util.IStateWriter.IsSeen, a);
				r.edgesGenerated++;
				if (unseen) {
					for (int k = 0; k < invariants.length; k++) {
						boolean holds;
						try {
							holds = tool.isValid(invariants[k], succ);
						} catch (final Throwable t) {
							r.error = (k < invNames.length ? invNames[k] : "invariant") + ": " + t;
							return true;
						}
						if (!holds) {
							r.violations.add(new Violation(k < invNames.length ? invNames[k] : invariants[k].getNameOfDefault(),
									to, store.level(to)));
							if (!continueOnViolation) {
								return true;
							}
						}
					}
				}
				if (seen.add(to)) {
					queue.add(to);
				}
			}
		}
		return false;
	}

	/** One invariant's verdict over a whole store. */
	public static final class Sweep {
		public final String invariant;
		public long violations;
		public Long firstFp;
		public Integer firstLevel;
		public String error;

		Sweep(String invariant) {
			this.invariant = invariant;
		}
	}

	/**
	 * Evaluate every invariant on every stored state: exact per-invariant
	 * verdicts for the refreshed graph, the first violation being the one at
	 * the lowest level. Costs one evaluation per (state, invariant), no
	 * successor generation.
	 */
	public static List<Sweep> sweep(final Tool tool, final GraphStore store) {
		final Action[] invariants = tool.getInvariants();
		final String[] names = tool.getInvNames();
		final List<Sweep> out = new ArrayList<>();
		for (int k = 0; k < invariants.length; k++) {
			out.add(new Sweep(k < names.length ? names[k] : invariants[k].getNameOfDefault()));
		}
		for (final long fp : store.fingerprints()) {
			final TLCState state = rebind(tool, store.read(fp));
			if (state == null) {
				continue;
			}
			final Integer level = store.level(fp);
			for (int k = 0; k < invariants.length; k++) {
				final Sweep sw = out.get(k);
				if (sw.error != null) {
					continue;
				}
				try {
					if (!tool.isValid(invariants[k], state)) {
						sw.violations++;
						if (sw.firstLevel == null || (level != null && level < sw.firstLevel)) {
							sw.firstLevel = level;
							sw.firstFp = fp;
						}
					}
				} catch (final Throwable t) {
					sw.error = t.getMessage() == null ? t.toString() : t.getMessage();
				}
			}
		}
		return out;
	}

	public static JsonObject diffJson(final ActionDiff d) {
		final JsonObject o = new JsonObject();
		o.add("unchanged", names(d.unchanged));
		o.add("changed", names(d.changed));
		o.add("added", names(d.added));
		o.add("removed", names(d.removed));
		o.add("changed_invariants", names(d.changedInvariants));
		o.add("changed_definitions", names(d.changedDefinitions));
		if (d.fullRerunReason != null) {
			o.addProperty("full_rerun_reason", d.fullRerunReason);
		}
		return o;
	}

	private static JsonArray names(final List<String> list) {
		final JsonArray a = new JsonArray();
		for (final String s : list) {
			a.add(s);
		}
		return a;
	}
}
