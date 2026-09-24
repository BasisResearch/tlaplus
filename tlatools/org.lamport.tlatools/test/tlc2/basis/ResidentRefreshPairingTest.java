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
import static tlc2.basis.ResidentHarness.storeEdges;
import static tlc2.basis.ResidentHarness.storeStates;

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * The disjuncts of an unnamed Next all share its name. Inserting one in front
 * must leave the others paired with themselves (unchanged, their edges
 * copied), not shift every pair by one.
 */
public class ResidentRefreshPairingTest {

	private static String spec(final boolean front) {
		return "---- MODULE P ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES x, y\n" //
				+ "Init == x = 0 /\\ y = 0\n" //
				+ "Next == " + (front ? "\\/ x = 99 /\\ x' = 0 /\\ y' = y\n        " : "") //
				+ "\\/ x < 5 /\\ x' = x + 1 /\\ y' = y\n" //
				+ "        \\/ y < 3 /\\ y' = y + 1 /\\ x' = x\n" //
				+ "====\n";
	}

	@Test
	public void testInsertedDisjunct() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("P.cfg", "INIT Init\nNEXT Next\n");
		h.write("P.tla", spec(false));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("P") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals(24, storeStates(check.getAsJsonObject("stats")));
		assertEquals(38, storeEdges(check.getAsJsonObject("stats")));

		h.write("P.tla", spec(true));
		final JsonObject r = h.ok("{\"command\":\"refresh\"}");
		assertEquals(r.toString(), "incremental", r.get("mode").getAsString());
		final JsonObject diff = r.getAsJsonObject("diff");
		assertEquals(r.toString(), 2, diff.getAsJsonArray("unchanged").size());
		assertEquals(r.toString(), 0, diff.getAsJsonArray("changed").size());
		assertEquals(r.toString(), 1, diff.getAsJsonArray("added").size());
		assertEquals(r.toString(), 0, diff.getAsJsonArray("removed").size());
		// Every old edge is copied; the new disjunct is never enabled.
		assertEquals(r.toString(), 38, r.get("edges_copied").getAsLong());
		assertEquals(r.toString(), 0, r.get("edges_generated").getAsLong());
		assertTrue(r.get("complete").getAsBoolean());
		assertEquals(24, storeStates(r));
		assertEquals(38, storeEdges(r));
		h.resident.shutdown();
	}
}
