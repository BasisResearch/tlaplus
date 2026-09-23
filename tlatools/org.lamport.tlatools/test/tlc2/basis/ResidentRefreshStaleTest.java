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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * After an incremental refresh, stats and registers still describe the run
 * before it: they say so, and whether the refreshed store is the whole graph.
 */
public class ResidentRefreshStaleTest {

	private static String spec(final int lim) {
		return "---- MODULE S ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES x, y\n" //
				+ "Init == x = 0 /\\ y = 0\n" //
				+ "Inc == x < " + lim + " /\\ x' = x + 1 /\\ y' = y\n" //
				+ "Bump == y < 3 /\\ y' = y + 1 /\\ x' = x\n" //
				+ "Next == Inc \\/ Bump\n" //
				+ "====\n";
	}

	@Test
	public void testStaleAfterRefresh() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("S.cfg", "INIT Init\nNEXT Next\n");
		h.write("S.tla", spec(5));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("S") + "\",\"workers\":1,\"deadlock\":false}");
		h.ok("{\"command\":\"check\"}");
		assertFalse(h.ok("{\"command\":\"stats\"}").has("stale"));
		assertFalse(h.ok("{\"command\":\"registers\"}").has("stale"));

		h.write("S.tla", spec(7));
		final JsonObject r = h.ok("{\"command\":\"refresh\"}");
		assertTrue(r.toString(), r.get("complete").getAsBoolean());
		for (final String command : new String[] { "stats", "registers" }) {
			final JsonObject o = h.ok("{\"command\":\"" + command + "\"}");
			assertTrue(o.toString(), o.get("stale").getAsBoolean());
			assertTrue(o.toString(), o.get("refresh_complete").getAsBoolean());
		}

		// A refresh cut by its budget leaves a store that is not the whole graph.
		h.write("S.tla", spec(9));
		final JsonObject cut = h.ok("{\"command\":\"refresh\",\"budget_ms\":-1}");
		assertFalse(cut.toString(), cut.get("complete").getAsBoolean());
		for (final String command : new String[] { "stats", "registers" }) {
			final JsonObject o = h.ok("{\"command\":\"" + command + "\"}");
			assertTrue(o.toString(), o.get("stale").getAsBoolean());
			assertFalse(o.toString(), o.get("refresh_complete").getAsBoolean());
		}
		h.resident.shutdown();
	}
}
