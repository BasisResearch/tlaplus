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

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * Parsing the edited spec in the same JVM must resolve the config's names to
 * the same definitions a fresh run would. Definition slots live on
 * process-global strings, so names the edit adds, before and after the ones
 * the config names, must not take the slots of INIT, NEXT or INVARIANT.
 */
public class ResidentRefreshDefinitionsTest {

	private static String spec(final int before, final int after) {
		final StringBuilder sb = new StringBuilder("---- MODULE D ----\nVARIABLES x, y\n");
		for (int i = 0; i < before; i++) {
			sb.append("Pb").append(i).append(" == ").append(i).append('\n');
		}
		sb.append("Init == x = \"a\" /\\ y = FALSE\n") //
				.append("A == x = \"a\" /\\ x' = \"b\" /\\ y' = TRUE\n") //
				.append("B == x = \"b\" /\\ x' = \"c\" /\\ y' = FALSE\n") //
				.append("Next == A \\/ B\n") //
				.append("Inv == y \\in BOOLEAN\n");
		for (int i = 0; i < after; i++) {
			sb.append("Pa").append(i).append(" == y = FALSE\n");
		}
		return sb.append("====\n").toString();
	}

	@Test
	public void testAddedDefinitions() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("D.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("D.tla", spec(0, 0));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("D") + "\",\"workers\":1,\"deadlock\":false}");
		assertEquals("ok", h.ok("{\"command\":\"check\"}").get("verdict").getAsString());

		// Before the fix, (8, 1) resolved INVARIANT Inv to Pa0 and (6, 3)
		// resolved NEXT to Pa1; (4, 1) and (0, 5) took Init's slot.
		final int[][] edits = { { 8, 1 }, { 6, 3 }, { 4, 1 }, { 0, 5 }, { 12, 12 } };
		for (final int[] e : edits) {
			h.write("D.tla", spec(e[0], e[1]));
			final JsonObject r = h.ok("{\"command\":\"refresh\"}");
			assertEquals(r.toString(), "incremental", r.get("mode").getAsString());
			assertTrue(r.toString(), r.get("complete").getAsBoolean());
			final JsonObject diff = r.getAsJsonObject("diff");
			assertEquals(r.toString(), "[\"A\",\"B\"]", diff.getAsJsonArray("unchanged").toString());
			assertEquals(r.toString(), 0, diff.getAsJsonArray("changed_invariants").size());
			assertEquals(r.toString(), "no_violation_found",
					r.getAsJsonArray("invariants").get(0).getAsJsonObject().get("verdict").getAsString());
			assertEquals(r.toString(), 3, ResidentHarness.storeStates(r));
		}
		h.resident.shutdown();
	}
}
