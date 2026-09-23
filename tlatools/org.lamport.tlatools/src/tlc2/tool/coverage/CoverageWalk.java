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
package tlc2.tool.coverage;

import java.util.HashSet;
import java.util.Set;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.tool.Action;
import tlc2.tool.ITool;
import tlc2.tool.coverage.ActionWrapper.Relation;
import tlc2.tool.coverage.OpApplNodeWrapper.Calculate;
import tlc2.util.Vect;

/**
 * The coverage tree as data.
 *
 * <p>
 * {@link CostModelCreator#report} walks the same {@link ActionWrapper} and
 * {@link OpApplNodeWrapper} tree and prints it, but the printer is lossy
 * exactly where a reader wants detail: {@link OpApplNodeWrapper#print}
 * skips subtrees whose counts are zero and collapses subtrees whose counts
 * agree with their parent. This walk keeps every node with its location,
 * primary and secondary counts and whether it is primed, and lists the
 * unevaluated subexpressions of every action and invariant separately, so
 * a conjunct that never ran is visible rather than elided. It lives in
 * this package because the counters are package-private.
 */
public final class CoverageWalk {

	private CoverageWalk() {
	}

	/** Whether the counters were armed for this run. */
	public static boolean enabled() {
		return TLCGlobals.isCoverageEnabled() || TLCGlobals.Coverage.isEnabled();
	}

	/**
	 * Per action: name, declaration, relation, how many successor states it
	 * produced ({@code found}) and how many were new ({@code distinct}); per
	 * invariant: its evaluations; per variable: the approximate number of
	 * distinct values seen. Every action's and invariant's subexpression tree
	 * goes under {@code tree}, and the subexpressions never evaluated under
	 * {@code unevaluated}.
	 */
	public static JsonObject walk(final ITool tool) {
		final JsonObject out = new JsonObject();
		out.addProperty("enabled", enabled());
		if (!enabled()) {
			return out;
		}
		final JsonArray actions = new JsonArray();
		final Set<CostModel> seen = new HashSet<>();
		for (final Action a : tool.getActions()) {
			if (!(a.cm instanceof ActionWrapper)) {
				continue;
			}
			final ActionWrapper w = (ActionWrapper) a.cm;
			final JsonObject o = new JsonObject();
			o.addProperty("name", a.getNameOfDefault());
			o.addProperty("id", a.getId());
			o.addProperty("location", a.getLocation());
			o.addProperty("relation", "next");
			// ActionWrapper.report: for NEXT, secondary is the distinct states
			// and the eval count the states found.
			o.addProperty("found", w.getEvalCount());
			o.addProperty("distinct", w.getSecondary());
			// Actions sharing a predicate share a cost model; the tree is
			// listed once and referenced by the others.
			if (seen.add(w)) {
				o.add("tree", subtree(w));
				o.add("unevaluated", unevaluated(w));
			} else {
				o.addProperty("tree_shared", true);
			}
			actions.add(o);
		}
		out.add("actions", actions);

		final JsonArray inits = new JsonArray();
		final Vect<Action> init = tool.getInitStateSpec();
		for (int i = 0; i < init.size(); i++) {
			final Action a = init.elementAt(i);
			if (!(a.cm instanceof ActionWrapper)) {
				continue;
			}
			final ActionWrapper w = (ActionWrapper) a.cm;
			final JsonObject o = new JsonObject();
			o.addProperty("location", a.getLocation());
			o.addProperty("found", w.getEvalCount());
			o.addProperty("distinct", w.getEvalCount() + w.getSecondary());
			o.add("tree", subtree(w));
			o.add("unevaluated", unevaluated(w));
			inits.add(o);
		}
		out.add("init", inits);

		final JsonArray invariants = new JsonArray();
		final String[] names = tool.getInvNames();
		final Action[] invs = tool.getInvariants();
		for (int i = 0; i < invs.length; i++) {
			final Action a = invs[i];
			if (!(a.cm instanceof ActionWrapper)) {
				continue;
			}
			final ActionWrapper w = (ActionWrapper) a.cm;
			final JsonObject o = new JsonObject();
			o.addProperty("name", i < names.length ? names[i] : a.getNameOfDefault());
			o.addProperty("location", a.getLocation());
			o.add("tree", subtree(w));
			o.add("unevaluated", unevaluated(w));
			invariants.add(o);
		}
		out.add("invariants", invariants);

		final JsonArray variables = new JsonArray();
		for (final OpDeclNode odn : tool.getSpecProcessor().getVariablesNodes()) {
			final JsonObject o = new JsonObject();
			o.addProperty("name", odn.getName().toString());
			o.addProperty("location", odn.getLocation().toString());
			final long count = odn.getCountDistinct() == null ? -1 : odn.getCountDistinct().count();
			// -1 means nothing counted (Noop, or before exploration).
			if (count >= 0) {
				o.addProperty("distinct_values_approx", count);
			} else {
				o.add("distinct_values_approx", null);
			}
			variables.add(o);
		}
		out.add("variables", variables);
		return out;
	}

	private static JsonArray subtree(final CostModelNode parent) {
		final JsonArray out = new JsonArray();
		for (final CostModelNode child : parent.children.values()) {
			out.add(node(child));
		}
		return out;
	}

	private static JsonObject node(final CostModelNode n) {
		final JsonObject o = new JsonObject();
		o.addProperty("location", n.getLocation().toString());
		if (n instanceof OpApplNodeWrapper) {
			final OpApplNodeWrapper w = (OpApplNodeWrapper) n;
			o.addProperty("primary", w.getEvalCount(Calculate.FRESH));
			o.addProperty("secondary", w.getSecondCount(Calculate.FRESH));
			o.addProperty("primed", w.isPrimed());
			final SemanticNode sn = w.getNode();
			if (sn != null) {
				o.addProperty("text", tlc2.basis.GraphStore.text(sn));
			}
		} else {
			o.addProperty("primary", n.getEvalCount());
			o.addProperty("secondary", n.getSecondary());
		}
		final JsonArray children = subtree(n);
		if (children.size() > 0) {
			o.add("children", children);
		}
		return o;
	}

	/**
	 * The subexpressions under {@code root} whose own evaluation count is
	 * zero and below which nothing ran, assignments included, listed flat
	 * with their locations. The inside of an assignment is not listed: its
	 * primed side is a target, never evaluated.
	 */
	private static JsonArray unevaluated(final CostModelNode root) {
		final JsonArray out = new JsonArray();
		collectUnevaluated(root, out);
		return out;
	}

	private static void collectUnevaluated(final CostModelNode parent, final JsonArray out) {
		if (parent instanceof OpApplNodeWrapper && ((OpApplNodeWrapper) parent).isPrimed()) {
			// Under a primed node (x' = e) the left side is an assignment
			// target and never evaluated; nothing there is a dead conjunct.
			return;
		}
		for (final CostModelNode child : parent.children.values()) {
			if (child instanceof OpApplNodeWrapper) {
				final OpApplNodeWrapper w = (OpApplNodeWrapper) child;
				// A conjunction's own counter can stay at zero while its
				// conjuncts run (the printer collapses such nodes into their
				// children), so a node is unevaluated only when nothing below
				// it ran either.
				// An assignment (x' = e, marked primed) counts when it runs, so
				// one whose count is zero with nothing below it run is dead too.
				if (w.getEvalCount(Calculate.FRESH) == 0L && !anyEvaluated(w)) {
					final JsonObject o = new JsonObject();
					o.addProperty("location", w.getLocation().toString());
					if (w.getNode() != null) {
						o.addProperty("text", tlc2.basis.GraphStore.text(w.getNode()));
					}
					out.add(o);
					// Its children are unevaluated too; one entry is enough.
					continue;
				}
			}
			collectUnevaluated(child, out);
		}
	}

	private static boolean anyEvaluated(final CostModelNode node) {
		for (final CostModelNode child : node.children.values()) {
			if (child instanceof OpApplNodeWrapper) {
				final OpApplNodeWrapper w = (OpApplNodeWrapper) child;
				if (w.getEvalCount(Calculate.FRESH) > 0L) {
					return true;
				}
			} else if (child.getEvalCount() > 0L) {
				return true;
			}
			if (anyEvaluated(child)) {
				return true;
			}
		}
		return false;
	}

	/** Which relation an action wrapper records, for callers outside the package. */
	public static boolean is(final CostModel cm, final Relation r) {
		return cm instanceof ActionWrapper && ((ActionWrapper) cm).is(r);
	}
}
