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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static tlc2.basis.ResidentHarness.storeEdges;
import static tlc2.basis.ResidentHarness.storeStates;

import java.io.File;

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * Incremental refresh against the graph a fresh run explores: a sequence of
 * edits (a changed guard, a changed definition, an added and a removed
 * action), each replay matching the fresh run's states and edges; then an
 * edit that breaks an invariant followed by its fix, which must replay from
 * the last complete graph rather than ask for a restart; then an edit that
 * does not evaluate, which must leave the store in place.
 */
public class ResidentRefreshTest {

	private static String spec(final int lim, final int blim, final String inv, final boolean extra,
			final boolean broken) {
		return "---- MODULE R ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES x, y\n" //
				+ "Lim == " + lim + "\n" //
				+ "Init == x = 0 /\\ y = 0\n" //
				+ "Inc == x < Lim /\\ x' = x + 1 /\\ y' = y\n" //
				+ "Bump == y < " + blim + " /\\ y' = y + 1 /\\ x' = x\n" //
				+ "Reset == x = Lim /\\ x' = 0 /\\ y' = y\n" //
				+ (extra ? "Extra == x = 2 /\\ x' = 6 /\\ y' = y\n" : "") //
				+ "Next == " + (broken ? "x = " : "") + "Inc \\/ Bump \\/ Reset" + (extra ? " \\/ Extra" : "") + "\n" //
				+ "Inv == " + inv + "\n" //
				+ "====\n";
	}

	@Test
	public void testRefresh() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("R.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("R.tla", spec(5, 3, "x + y < 100", false, false));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("R") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals("ok", check.get("verdict").getAsString());
		assertEquals(24, storeStates(check.getAsJsonObject("stats")));
		assertEquals(42, storeEdges(check.getAsJsonObject("stats")));

		// Each edit's expected (states, edges) is what a fresh run stores.
		final Object[][] edits = { //
				{ spec(5, 4, "x + y < 100", false, false), 30, 54, "Bump" }, // a changed guard
				{ spec(7, 4, "x + y < 100", false, false), 40, 72, "Inc" }, // a changed definition
				{ spec(7, 4, "x + y < 100", true, false), 40, 77, null }, // an added action
				{ spec(7, 2, "x + y < 100", false, false), 24, 40, "Bump" }, // removed, and changed
		};
		for (final Object[] e : edits) {
			h.write("R.tla", (String) e[0]);
			final JsonObject r = h.ok("{\"command\":\"refresh\"}");
			assertEquals(r.toString(), "incremental", r.get("mode").getAsString());
			assertTrue(r.get("complete").getAsBoolean());
			assertEquals(r.toString(), ((Integer) e[1]).longValue(), storeStates(r));
			assertEquals(r.toString(), ((Integer) e[2]).longValue(), storeEdges(r));
			if (e[3] != null) {
				assertTrue(r.toString(), r.getAsJsonObject("diff").getAsJsonArray("changed").toString()
						.contains((String) e[3]));
			}
			assertTrue(r.has("unchecked"));
		}

		// An edit that breaks the invariant stops at its first violation...
		h.write("R.tla", spec(7, 2, "x + y < 6", false, false));
		JsonObject r = h.ok("{\"command\":\"refresh\"}");
		assertEquals("incremental", r.get("mode").getAsString());
		assertFalse(r.get("complete").getAsBoolean());
		assertTrue(r.get("stopped_at_first_violation").getAsBoolean());
		assertEquals("violated", r.getAsJsonArray("invariants").get(0).getAsJsonObject().get("verdict").getAsString());

		// ...and the fix replays from the last complete graph, not a restart.
		h.write("R.tla", spec(7, 2, "x + y < 100", false, false));
		r = h.ok("{\"command\":\"refresh\"}");
		assertEquals(r.toString(), "incremental", r.get("mode").getAsString());
		assertEquals("last_complete", r.get("replayed_from").getAsString());
		assertTrue(r.get("complete").getAsBoolean());
		assertEquals(24, storeStates(r));
		assertEquals(40, storeEdges(r));

		// An edit that does not evaluate is not adopted: the store stays.
		final JsonObject screen = h.ok("{\"command\":\"screen\",\"candidates\":[\"x < 1\"]}");
		final long fp = screen.getAsJsonArray("results").get(0).getAsJsonObject().get("first_violation_fp")
				.getAsLong();
		h.write("R.tla", spec(7, 2, "x + y < 100", false, true));
		r = h.ok("{\"command\":\"refresh\"}");
		assertFalse(r.toString(), r.get("adopted").getAsBoolean());
		assertTrue(r.has("error"));
		assertEquals(24, storeStates(r));
		final JsonObject eval = h.ok("{\"command\":\"eval\",\"fp\":" + fp + ",\"expr\":\"x + y\"}");
		assertTrue(eval.toString(), eval.get("evaluated").getAsBoolean());

		// Guards are not tallied during a replay; the profile says so.
		assertTrue(h.ok("{\"command\":\"guard_profile\"}").get("stale").getAsBoolean());

		// Stores nothing refers to are released: only the current store's
		// file is left (a metadir that held nothing else goes with it).
		final String current = h.ok("{\"command\":\"store\"}").toString();
		int files = 0;
		for (final File metadir : new File(h.dir.toFile(), "states").listFiles()) {
			if (new File(metadir, "basis.states").exists()) {
				files++;
			}
		}
		assertEquals(current, 1, files);
		h.resident.shutdown();
	}
}
