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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static tlc2.basis.ResidentHarness.storeStates;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

/**
 * Under a VIEW, several concrete states share a fingerprint and TLC explores
 * only the one whose fingerprint-set put won. The store must keep that one:
 * its recorded out-edges are the successors TLC generated from it, and the
 * store queries, the invariant sweeps and a refresh all work from its
 * content. Here the hidden variable decides the successors, so content from
 * the wrong concrete state would disagree with the recorded edges. Run with
 * several workers, whose writes race for the store's lock; the check is the
 * same after a refresh, which replays that content and must not carry a
 * state's old edges onto different content the edit reaches first.
 */
public class ResidentViewStoreTest {

	private static String spec(final boolean extra) {
		return "---- MODULE V ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES x, y\n" //
				+ "Init == x = 0 /\\ y = 0\n" //
				+ "A == x < 6 /\\ x' = x + 1 + y /\\ y' = 0\n" //
				+ "B == x < 6 /\\ x' = x + 1 /\\ y' = 1\n" //
				+ (extra ? "C == x = 1 /\\ x' = 4 /\\ y' = 1 - y\n" : "") //
				+ "Next == A \\/ B" + (extra ? " \\/ C" : "") + "\n" //
				+ "View == x\n" //
				+ "Inv == x <= 7\n" //
				+ "====\n";
	}

	/**
	 * Walk the store from its initial state through the successors each
	 * stored state's content generates, and check them against the edges the
	 * store recorded out of that state. Returns the number of states walked.
	 */
	private static int consistent(final ResidentHarness h) throws Exception {
		final JsonObject screen = h.ok("{\"command\":\"screen\",\"candidates\":[\"x # 0\"]}");
		final long init = screen.getAsJsonArray("results").get(0).getAsJsonObject().get("first_violation_fp")
				.getAsLong();
		final Map<Long, Set<String>> generated = new HashMap<>();
		final Map<Long, Set<String>> recorded = new HashMap<>();
		final ArrayDeque<Long> queue = new ArrayDeque<>();
		final Set<Long> seen = new HashSet<>();
		queue.add(init);
		seen.add(init);
		while (!queue.isEmpty()) {
			final long fp = queue.poll();
			final JsonObject n = h.ok("{\"command\":\"neighbours\",\"fp\":\"" + fp + "\"}");
			final Set<String> out = generated.computeIfAbsent(fp, k -> new HashSet<>());
			final JsonArray succs = n.getAsJsonArray("successors");
			for (int i = 0; i < succs.size(); i++) {
				final JsonObject a = succs.get(i).getAsJsonObject();
				final JsonArray states = a.getAsJsonArray("states");
				for (int j = 0; j < states.size(); j++) {
					final JsonObject s = states.get(j).getAsJsonObject();
					assertTrue(n.toString(), s.get("stored").getAsBoolean());
					final long to = s.get("fp").getAsLong();
					out.add(to + "/" + a.get("action_id").getAsLong());
					if (seen.add(to)) {
						queue.add(to);
					}
				}
			}
			final JsonArray preds = n.getAsJsonArray("predecessors");
			for (int i = 0; i < preds.size(); i++) {
				final JsonObject p = preds.get(i).getAsJsonObject();
				recorded.computeIfAbsent(p.get("fp").getAsLong(), k -> new HashSet<>())
						.add(fp + "/" + p.get("action_id").getAsLong());
			}
		}
		for (final long fp : seen) {
			assertEquals("state " + fp, generated.get(fp), recorded.getOrDefault(fp, new HashSet<>()));
		}
		return seen.size();
	}

	@Test
	public void testViewStore() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("V.cfg", "INIT Init\nNEXT Next\nVIEW View\nINVARIANT Inv\n");
		h.write("V.tla", spec(false));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("V") + "\",\"workers\":4,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals(check.toString(), "ok", check.get("verdict").getAsString());
		final JsonObject stats = check.getAsJsonObject("stats");
		assertEquals(stats.get("distinct").getAsLong(), storeStates(stats));
		assertEquals(storeStates(stats), consistent(h));

		h.write("V.tla", spec(true));
		final JsonObject r = h.ok("{\"command\":\"refresh\"}");
		assertEquals(r.toString(), "incremental", r.get("mode").getAsString());
		assertTrue(r.toString(), r.get("complete").getAsBoolean());
		assertEquals(storeStates(r), consistent(h));
		// What a fresh run of the edited spec stores (one worker, so which
		// concrete state TLC keeps is fixed). The edit reaches x = 4 first
		// with y = 1, whose successors reach x = 7; the old content's edges
		// do not.
		assertEquals(r.toString(), 8, storeStates(r));
		assertEquals(r.toString(), 13, ResidentHarness.storeEdges(r));
		assertEquals("no_violation_found",
				r.getAsJsonArray("invariants").get(0).getAsJsonObject().get("verdict").getAsString());
		h.resident.shutdown();
	}
}
