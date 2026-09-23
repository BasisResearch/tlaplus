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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.Action;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.util.Vect;

/**
 * Re-explore after a spec edit, doing only the work the edit requires.
 *
 * <p>
 * The edited spec is parsed into a new {@link Tool}. Every action, invariant,
 * initial predicate and constraint gets a signature: its
 * own source text, the text of every user definition it reaches
 * (transitively, across modules), and the values its context binds (the
 * {@code p} of an action split out of {@code \E p \in S : A(p)}). Actions are
 * paired with the old ones by name and signature; invariants by name. If the
 * variables, the initial predicate or a state or action constraint changed,
 * the spec has a VIEW or a SYMMETRY set, or anything explored reads {@code TLCGet} (whose
 * values depend on the path to a state, not the state), nothing can be
 * reused and the caller runs a fresh exploration instead; so does the caller
 * when the model config changed or the old exploration did not finish.
 *
 * <p>
 * Otherwise the old store's graph is replayed: the states reachable from the
 * initial states along edges of unchanged actions survive, each copied into
 * a new store with those edges; surviving states are re-expanded under the
 * changed and added actions only; states reached for the first time are
 * expanded under every action. Every new state is checked against every
 * invariant, and every surviving state against the changed invariants.
 * Successors a constraint excludes are checked too, as TLC checks them, and
 * kept in the store unexpanded; edges to them under unchanged actions are
 * carried like any other.
 * Successor generation, constraints and invariant evaluation all go through
 * the new {@link Tool}, so the store is a cache of TLC's own answers, never
 * an oracle of its own. Copying an edge is sound only because the old store
 * holds a fully explored graph under the same constraints: every in-model
 * successor of a stored state under an unchanged action is already an edge.
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
	public static ActionDiff diff(final Tool oldTool, final Tool newTool) {
		final ActionDiff d = new ActionDiff();
		// Variables, from each tool's own declarations: TLC's static variable
		// table (behind the store's decoding) already belongs to the new parse.
		if (!variableNames(oldTool).equals(variableNames(newTool))) {
			d.fullRerunReason = "the variables changed";
			return d;
		}
		// Definitions of the root module, by name (reported, not decisive:
		// the signatures below decide what changed).
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
		// What every explored state and edge was filtered or identified by.
		if (!initSignature(oldTool).equals(initSignature(newTool))) {
			d.fullRerunReason = "the initial predicate changed";
			return d;
		}
		if (!constraintSignature(oldTool).equals(constraintSignature(newTool))) {
			d.fullRerunReason = "a state or action constraint changed";
			return d;
		}
		for (final Tool t : new Tool[] { oldTool, newTool }) {
			final String reason = fingerprintAbstraction(t);
			if (reason != null) {
				d.fullRerunReason = reason;
				return d;
			}
		}
		if (!substitutionSignature(oldTool).equals(substitutionSignature(newTool))) {
			d.fullRerunReason = "a definition the config substitutes with <- changed";
			return d;
		}
		for (final Tool t : new Tool[] { oldTool, newTool }) {
			final String reason = tlcGetUse(t);
			if (reason != null) {
				d.fullRerunReason = reason;
				return d;
			}
		}
		// Actions.
		final Map<String, List<Action>> oldByKey = new HashMap<>();
		final Map<Integer, String> oldSig = new HashMap<>();
		for (final Action a : oldTool.getActions()) {
			oldByKey.computeIfAbsent(a.getNameOfDefault(), k -> new ArrayList<>()).add(a);
			oldSig.put(a.getId(), signature(a));
		}
		// Exact (name, signature) pairs first, over every new action, so an
		// edited action cannot claim an old one that a later new action
		// matches exactly: the disjuncts of an unnamed Next all share its
		// name, and inserting one in front would otherwise shift every pair.
		final Set<Integer> matchedOld = new HashSet<>();
		final Action[] newActions = newTool.getActions();
		final Action[] exact = new Action[newActions.length];
		for (int i = 0; i < newActions.length; i++) {
			final String sig = signature(newActions[i]);
			for (final Action o : oldByKey.getOrDefault(newActions[i].getNameOfDefault(), List.of())) {
				if (!matchedOld.contains(o.getId()) && oldSig.get(o.getId()).equals(sig)) {
					matchedOld.add(o.getId());
					exact[i] = o;
					break;
				}
			}
		}
		// Then the rest: a same-named old action left over makes it changed.
		for (int i = 0; i < newActions.length; i++) {
			final Action n = newActions[i];
			final String name = n.getNameOfDefault();
			if (exact[i] != null) {
				d.carried.put(exact[i].getId(), n);
				d.unchanged.add(name);
			} else if (pairUnmatched(oldByKey.getOrDefault(name, List.of()), matchedOld)) {
				// Same name, different signature.
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
			oldInv.put(i < oldNames.length ? oldNames[i] : oldInvs[i].getNameOfDefault(), signature(oldInvs[i]));
		}
		final String[] newNames = newTool.getInvNames();
		final Action[] newInvs = newTool.getInvariants();
		for (int i = 0; i < newInvs.length; i++) {
			final String name = i < newNames.length ? newNames[i] : newInvs[i].getNameOfDefault();
			if (!signature(newInvs[i]).equals(oldInv.get(name))) {
				d.changedInvariants.add(name);
			}
		}
		return d;
	}

	/**
	 * Why a replay cannot be trusted because {@code tool} reads TLC's
	 * registers, or null. {@code TLCGet("level")} and its siblings depend on
	 * how a state was reached, not only on its fingerprint: an added action
	 * can shorten the path to a state and bring successors a level-bounded
	 * constraint excluded back into the model, which copied edges never
	 * re-examine. Replay also evaluates without the predecessor TLC sets.
	 */
	private static String tlcGetUse(final Tool tool) {
		for (final Action a : tool.getActions()) {
			if (reachesTLCGet(a.pred)) {
				return "the action " + a.getNameOfDefault() + " reads TLCGet, which depends on the path to a state";
			}
		}
		final Vect<Action> init = tool.getInitStateSpec();
		for (int i = 0; i < init.size(); i++) {
			if (reachesTLCGet(init.elementAt(i).pred)) {
				return "the initial predicate reads TLCGet, which depends on the path to a state";
			}
		}
		for (final ExprNode c : tool.getModelConstraints()) {
			if (reachesTLCGet(c)) {
				return "a state constraint reads TLCGet, which depends on the path to a state";
			}
		}
		for (final ExprNode c : tool.getActionConstraints()) {
			if (reachesTLCGet(c)) {
				return "an action constraint reads TLCGet, which depends on the path to a state";
			}
		}
		for (final Action a : tool.getInvariants()) {
			if (reachesTLCGet(a.pred)) {
				return "the invariant " + a.getNameOfDefault() + " reads TLCGet, which depends on the path to a state";
			}
		}
		return null;
	}

	private static boolean reachesTLCGet(final SemanticNode node) {
		final Map<String, String> reached = new TreeMap<>();
		reach(node, reached, new HashSet<>());
		return reached.containsKey("TLC!TLCGet");
	}

	/** Claim the first old action of {@code candidates} not yet paired; false when none is left. */
	private static boolean pairUnmatched(final List<Action> candidates, final Set<Integer> matchedOld) {
		for (final Action o : candidates) {
			if (matchedOld.add(o.getId())) {
				return true;
			}
		}
		return false;
	}

	private static List<String> variableNames(final Tool tool) {
		final List<String> out = new ArrayList<>();
		for (final OpDeclNode v : tool.getSpecProcessor().getVariablesNodes()) {
			out.add(v.getName().toString());
		}
		return out;
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

	private static String signature(final Action a) {
		return signature(a.pred, a.con);
	}

	/**
	 * The text of {@code node}, the name, formal parameters and text of every
	 * user definition it reaches (transitively, in name order), the
	 * substitutions of every INSTANCE it passes through and the values
	 * {@code con} binds.
	 * Two nodes with equal signatures denote the same predicate under the same
	 * constant values, which the config pins.
	 */
	private static String signature(final SemanticNode node, final Context con) {
		final StringBuilder sb = new StringBuilder(GraphStore.text(node));
		final Map<String, String> reached = new TreeMap<>();
		reach(node, reached, new HashSet<>());
		for (final Map.Entry<String, String> e : reached.entrySet()) {
			sb.append('\n').append(e.getKey()).append(" == ").append(e.getValue());
		}
		if (con != null && con != Context.Empty) {
			sb.append("\nwith ").append(con);
		}
		return sb.toString();
	}

	private static void reach(final SemanticNode node, final Map<String, String> reached,
			final Set<SemanticNode> seen) {
		if (node == null || !seen.add(node)) {
			return;
		}
		if (node instanceof OpApplNode) {
			reachDefinition(((OpApplNode) node).getOperator(), reached, seen);
		} else if (node instanceof OpArgNode) {
			reachDefinition(((OpArgNode) node).getOp(), reached, seen);
		} else if (node instanceof SubstInNode) {
			// INSTANCE ... WITH a <- e: which parameter each expression
			// replaces is not in any definition's text.
			final StringBuilder with = new StringBuilder();
			for (final Subst s : ((SubstInNode) node).getSubsts()) {
				with.append(s.getOp().getName()).append(" <- ").append(GraphStore.text(s.getExpr())).append(", ");
			}
			// Keyed by content, not location, so moving the text is no edit.
			reached.put("WITH " + with, "");
		}
		final SemanticNode[] children = node.getChildren();
		if (children != null) {
			for (final SemanticNode c : children) {
				reach(c, reached, seen);
			}
		}
	}

	private static void reachDefinition(final SymbolNode op, final Map<String, String> reached,
			final Set<SemanticNode> seen) {
		if (!(op instanceof OpDefNode)) {
			return;
		}
		final OpDefNode def = (OpDefNode) op;
		if (def.getKind() != ASTConstants.UserDefinedOpKind || def.getBody() == null) {
			return;
		}
		// Keyed by module too: two modules may define the same name.
		final String module = def.getLocation() == null ? "" : def.getLocation().source() + "!";
		// The formal parameters too: F(a, b) == a - b and F(b, a) == a - b
		// share their body text.
		final StringBuilder params = new StringBuilder("(");
		for (final FormalParamNode p : def.getParams()) {
			params.append(p.getName()).append('/').append(p.getArity()).append(", ");
		}
		reached.put(module + def.getName(), params.append(") ").append(GraphStore.text(def.getBody())).toString());
		reach(def.getBody(), reached, seen);
	}

	private static String initSignature(final Tool tool) {
		final StringBuilder sb = new StringBuilder();
		final Vect<Action> init = tool.getInitStateSpec();
		for (int i = 0; i < init.size(); i++) {
			sb.append(signature(init.elementAt(i))).append('\n');
		}
		return sb.toString();
	}

	private static String constraintSignature(final Tool tool) {
		final StringBuilder sb = new StringBuilder();
		for (final ExprNode c : tool.getModelConstraints()) {
			sb.append("state ").append(signature(c, null)).append('\n');
		}
		for (final ExprNode c : tool.getActionConstraints()) {
			sb.append("action ").append(signature(c, null)).append('\n');
		}
		return sb.toString();
	}

	/**
	 * The definitions the config substitutes in ({@code CONSTANT N <- Def},
	 * {@code Op <- Def}, {@code Op <- [M] Def}). TLC binds them as tool
	 * objects, so the syntactic walk in {@link #signature} never reaches them:
	 * an edit to {@code Def} would leave every action's signature unchanged.
	 */
	private static String substitutionSignature(final Tool tool) {
		final Map<String, OpDefNode> byName = new HashMap<>();
		final OpDefNode[] defs = tool.getSpecProcessor().getRootModule().getOpDefs();
		for (final OpDefNode def : defs == null ? new OpDefNode[0] : defs) {
			byName.put(def.getName().toString(), def);
		}
		final Map<String, String> subst = new TreeMap<>();
		final Map<String, String> overrides = tool.getModelConfig().getOverrides();
		for (final Map.Entry<String, String> e : overrides.entrySet()) {
			subst.put(e.getKey(), substituted(e.getValue(), byName));
		}
		final Map<?, ?> modOverrides = tool.getModelConfig().getModOverrides();
		for (final Map.Entry<?, ?> m : modOverrides.entrySet()) {
			for (final Map.Entry<?, ?> e : ((Map<?, ?>) m.getValue()).entrySet()) {
				subst.put(m.getKey() + "!" + e.getKey(), substituted(String.valueOf(e.getValue()), byName));
			}
		}
		final StringBuilder sb = new StringBuilder();
		for (final Map.Entry<String, String> e : subst.entrySet()) {
			sb.append(e.getKey()).append(" <- ").append(e.getValue()).append('\n');
		}
		return sb.toString();
	}

	private static String substituted(final String rhs, final Map<String, OpDefNode> byName) {
		final OpDefNode def = byName.get(rhs);
		return def == null || def.getBody() == null ? rhs : rhs + " == " + signature(def.getBody(), null);
	}

	/**
	 * Why a replay cannot be trusted because {@code tool} fingerprints states
	 * through a VIEW or a SYMMETRY set, or null. A fingerprint then names
	 * several concrete states and TLC explores the one that reached it first.
	 * The store keeps that one's content, which a copied edge from another
	 * state need not generate, so a replay can explore a representative the
	 * edited spec never reaches.
	 */
	private static String fingerprintAbstraction(final Tool tool) {
		if (tool.getViewSpec() != null) {
			return "the spec has a VIEW, under which a stored state may not be the one a copied edge reaches";
		}
		final String symmetry = tool.getModelConfig().getSymmetry();
		if (tool.getSymmetryPerms() != null || (symmetry != null && !symmetry.isEmpty())) {
			return "the spec has a SYMMETRY set, under which a stored state may not be the one a copied edge reaches";
		}
		return null;
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
		// Initial states the (unchanged) constraints exclude: never explored,
		// but TLC checks invariants on them, so the changed ones are checked.
		// All are stored before any is checked, so the state-level properties
		// see every initial state however the replay stops.
		final List<TLCState> excludedInitial = new ArrayList<>();
		for (final long fp : oldStore.excludedInitialFingerprints()) {
			final TLCState s = rebind(newTool, oldStore.read(fp));
			if (s != null) {
				newStore.writeExcludedInitial(s);
				excludedInitial.add(s);
			}
		}
		for (final TLCState s : excludedInitial) {
			if (checkInvariants(newTool, s, s.fingerPrint(), 1, invariants, invNames, changedInv, continueOnViolation, r)) {
				stop = true;
				break;
			}
		}
		while (!queue.isEmpty() && !stop) {
			if (System.currentTimeMillis() - started > budgetMs) {
				r.budgetExhausted = true;
				break;
			}
			final long fp = queue.poll();
			final TLCState state = rebind(newTool, newStore.read(fp));
			// No VIEW or SYMMETRY (see fingerprintAbstraction): a fingerprint
			// names one state, so a stored one keeps its old edges.
			final boolean survivor = oldStates.contains(fp);
			if (survivor) {
				r.survivors++;
				// Carried edges: copy successors and their content.
				try {
					for (final long[] e : forward.getOrDefault(fp, List.of())) {
						final long to = e[0];
						final Action a = newTool.getActions()[actionIndex(newTool, (int) e[1])];
						final TLCState succ = newStore.contains(to) ? newStore.read(to)
								: rebind(newTool, oldStore.read(to));
						if (succ == null) {
							continue;
						}
						final boolean unseen = !newStore.contains(to);
						newStore.writeState(state, succ,
								unseen ? tlc2.util.IStateWriter.IsUnseen : tlc2.util.IStateWriter.IsSeen, a);
						r.edgesCopied++;
						if (seen.add(to)) {
							queue.add(to);
						}
					}
				} catch (final Throwable t) {
					r.error = "copying edges: " + t;
					break;
				}
				// Changed invariants on a survivor.
				if (checkInvariants(newTool, state, fp, newStore.level(fp), invariants, invNames, changedInv,
						continueOnViolation, r)) {
					break;
				}
				// Carried edges to excluded successors: the same successors under
				// the same constraints, so still excluded. TLC checked every
				// invariant on them; the changed ones are checked again.
				try {
					for (final long[] e : oldStore.excludedSuccessors(fp)) {
						final Action a = diff.carried.get((int) e[1]);
						if (a == null) {
							continue;
						}
						final long to = e[0];
						final boolean fresh = !newStore.contains(to) && !newStore.isExcluded(to);
						final TLCState succ = fresh ? rebind(newTool, oldStore.read(to)) : newStore.read(to);
						if (succ == null) {
							continue;
						}
						newStore.writeExcluded(state, succ, a);
						r.edgesCopied++;
						if (fresh && checkInvariants(newTool, succ, to, newStore.level(to), invariants, invNames,
								changedInv, continueOnViolation, r)) {
							stop = true;
							break;
						}
					}
				} catch (final Throwable t) {
					r.error = "copying excluded edges: " + t;
					break;
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

	/**
	 * Expand one state under {@code actions}; returns true to stop. As TLC's
	 * worker does, every invariant is checked on a successor seen for the
	 * first time, including one a constraint excludes from the model: the
	 * excluded one is kept in the store, not expanded.
	 */
	private static boolean expand(final Tool tool, final GraphStore store, final TLCState state, final long fp,
			final List<Action> actions, final Action[] invariants, final String[] invNames,
			final boolean continueOnViolation, final Set<Long> seen, final ArrayDeque<Long> queue, final Result r) {
		for (final Action a : actions) {
			final StateVec next;
			try {
				next = tool.getNextStatesUnrecorded(a, state);
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
					inModel = inModel(tool, state, succ);
				} catch (final Throwable t) {
					r.error = "constraint: " + t;
					return true;
				}
				final long to = succ.fingerPrint();
				if (!inModel) {
					final boolean fresh = !store.contains(to) && !store.isExcluded(to);
					store.writeExcluded(state, succ, a);
					if (fresh && checkInvariants(tool, succ, to, store.level(to), invariants, invNames, null,
							continueOnViolation, r)) {
						return true;
					}
					continue;
				}
				final boolean unseen = !store.contains(to);
				store.writeState(state, succ, unseen ? tlc2.util.IStateWriter.IsUnseen : tlc2.util.IStateWriter.IsSeen, a);
				r.edgesGenerated++;
				if (unseen && checkInvariants(tool, succ, to, store.level(to), invariants, invNames, null,
						continueOnViolation, r)) {
					return true;
				}
				if (seen.add(to)) {
					queue.add(to);
				}
			}
		}
		return false;
	}

	/**
	 * Whether {@code succ}, reached from {@code state}, satisfies every state
	 * and action constraint, as {@link Tool#isInModel(TLCState)} and
	 * {@link Tool#isInActions(TLCState, TLCState)} decide it. Those read the
	 * constraints' cost models, which only a tool a checker ran has, so a
	 * refreshed tool evaluates them without one.
	 */
	private static boolean inModel(final Tool tool, final TLCState state, final TLCState succ) {
		for (final ExprNode c : tool.getModelConstraints()) {
			if (!bool(tool.eval(c, Context.Empty, succ, tlc2.tool.coverage.CostModel.DO_NOT_RECORD), c)) {
				return false;
			}
		}
		for (final ExprNode c : tool.getActionConstraints()) {
			if (!bool(tool.eval(c, Context.Empty, state, succ, tlc2.tool.EvalControl.Clear,
					tlc2.tool.coverage.CostModel.DO_NOT_RECORD), c)) {
				return false;
			}
		}
		return true;
	}

	private static boolean bool(final tlc2.value.IValue v, final ExprNode constraint) {
		if (!(v instanceof tlc2.value.impl.BoolValue)) {
			throw new IllegalStateException("constraint " + GraphStore.text(constraint) + " is not a boolean: " + v);
		}
		return ((tlc2.value.impl.BoolValue) v).val;
	}

	/**
	 * Check the invariants named in {@code only} (every one when null) on
	 * {@code state}, recording violations; returns true to stop, on an error
	 * or on a violation unless {@code continueOnViolation}.
	 */
	private static boolean checkInvariants(final Tool tool, final TLCState state, final long fp, final Integer level,
			final Action[] invariants, final String[] invNames, final Set<String> only,
			final boolean continueOnViolation, final Result r) {
		for (int k = 0; k < invariants.length; k++) {
			final String name = k < invNames.length ? invNames[k] : invariants[k].getNameOfDefault();
			if (only != null && !only.contains(name)) {
				continue;
			}
			boolean holds;
			try {
				holds = holds(tool, invariants[k], state);
			} catch (final Throwable t) {
				r.error = name + ": " + t;
				return true;
			}
			if (!holds) {
				r.violations.add(new Violation(name, fp, level == null ? -1 : level));
				if (!continueOnViolation) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Whether the state predicate {@code inv} holds in {@code state}, as
	 * {@link Tool#isValid(Action, TLCState)} decides it but without counting
	 * the evaluation in the invariant's coverage: a sweep over the store is
	 * not part of the run whose coverage is reported.
	 */
	static boolean holds(final Tool tool, final Action inv, final TLCState state) {
		final tlc2.value.IValue v = tool.eval(inv.pred, inv.con, state, tlc2.tool.coverage.CostModel.DO_NOT_RECORD);
		if (!(v instanceof tlc2.value.impl.BoolValue)) {
			throw new IllegalStateException("invariant " + inv.getNameOfDefault() + " is not a boolean: " + v);
		}
		return ((tlc2.value.impl.BoolValue) v).val;
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
	 * Evaluate every invariant on every stored state, excluded successors and
	 * excluded initial states included, as TLC evaluates them: exact per-invariant
	 * verdicts for the refreshed graph, the first violation being the one at
	 * the lowest level. Costs one evaluation per (state, invariant), no
	 * successor generation.
	 */
	public static List<Sweep> sweep(final Tool tool, final GraphStore store) {
		return sweep(tool, store, null);
	}

	/**
	 * {@link #sweep(Tool, GraphStore)} over the invariants named in
	 * {@code only} (every invariant when null); one {@link Sweep} per
	 * configured invariant, in order, with those left out untouched.
	 */
	public static List<Sweep> sweep(final Tool tool, final GraphStore store, final Set<String> only) {
		final Action[] invariants = tool.getInvariants();
		final String[] names = tool.getInvNames();
		final List<Sweep> out = new ArrayList<>();
		final boolean[] wanted = new boolean[invariants.length];
		for (int k = 0; k < invariants.length; k++) {
			final String name = k < names.length ? names[k] : invariants[k].getNameOfDefault();
			out.add(new Sweep(name));
			wanted[k] = only == null || only.contains(name);
		}
		// The excluded successors too: TLC checks invariants on them.
		final long[] inModel = store.fingerprints();
		final long[] excluded = store.excludedFingerprints();
		final long[] all = java.util.Arrays.copyOf(inModel, inModel.length + excluded.length);
		System.arraycopy(excluded, 0, all, inModel.length, excluded.length);
		for (final long fp : all) {
			final TLCState state = rebind(tool, store.read(fp));
			if (state == null) {
				continue;
			}
			final Integer level = store.level(fp);
			for (int k = 0; k < invariants.length; k++) {
				final Sweep sw = out.get(k);
				if (!wanted[k] || sw.error != null) {
					continue;
				}
				try {
					if (!holds(tool, invariants[k], state)) {
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

	/**
	 * Evaluate every state-level PROPERTY (TLC's implied inits, which it
	 * checks on the initial states only) on the stored initial states, those a
	 * state constraint excluded included: one
	 * {@link Sweep} per implied init, in order.
	 */
	public static List<Sweep> impliedInits(final Tool tool, final GraphStore store) {
		final Action[] inits = tool.getImpliedInits();
		final String[] names = tool.getImpliedInitNames();
		final List<Sweep> out = new ArrayList<>();
		for (int k = 0; k < inits.length; k++) {
			out.add(new Sweep(k < names.length ? names[k] : inits[k].getNameOfDefault()));
		}
		final long[] inModel = store.initialFingerprints();
		final long[] excluded = store.excludedInitialFingerprints();
		final long[] all = java.util.Arrays.copyOf(inModel, inModel.length + excluded.length);
		System.arraycopy(excluded, 0, all, inModel.length, excluded.length);
		for (final long fp : all) {
			final TLCState state = rebind(tool, store.read(fp));
			if (state == null) {
				continue;
			}
			for (int k = 0; k < inits.length; k++) {
				final Sweep sw = out.get(k);
				if (sw.error != null) {
					continue;
				}
				try {
					if (!holds(tool, inits[k], state)) {
						sw.violations++;
						if (sw.firstFp == null) {
							sw.firstFp = fp;
							sw.firstLevel = 1;
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
