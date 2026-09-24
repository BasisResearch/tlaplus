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
 * A budgeted check that continues past violations, on several workers, over
 * a spec whose invariant fails on most states. Pausing must not deadlock
 * with workers reporting violations, and reports past the per-property
 * trace cap must be counted rather than kept as messages.
 */
public class ResidentContinuationBudgetTest {

	@Test(timeout = 120_000)
	public void testBudgetedContinuation() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("C.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("C.tla", "---- MODULE C ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES a, b, c\n" //
				+ "N == 20\n" //
				+ "Init == a = 0 /\\ b = 0 /\\ c = 0\n" //
				+ "A == a < N-1 /\\ a' = a + 1 /\\ UNCHANGED <<b, c>>\n" //
				+ "B == b < N-1 /\\ b' = b + 1 /\\ UNCHANGED <<a, c>>\n" //
				+ "C == c < N-1 /\\ c' = c + 1 /\\ UNCHANGED <<a, b>>\n" //
				+ "Next == A \\/ B \\/ C\n" //
				+ "Inv == a < 3\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("C") + "\",\"workers\":4,\"deadlock\":false,\"store\":false}");

		JsonObject check = null;
		long messages = 0;
		int pauses = 0;
		for (int i = 0; i < 10_000; i++) {
			check = h.ok("{\"command\":\"check\",\"continue\":true,\"budget_ms\":5}");
			messages += check.getAsJsonArray("messages").size();
			if (check.get("finished").getAsBoolean()) {
				break;
			}
			pauses++;
		}
		assertTrue(check.toString(), check.get("finished").getAsBoolean());
		assertTrue("the budget never paused the run", pauses > 0);
		assertEquals("invariant_violated", check.get("verdict").getAsString());
		assertEquals(8000, check.getAsJsonObject("stats").get("distinct").getAsLong());
		// Every state with a >= 3 violates Inv: 17 * 20 * 20 reports, one traced.
		final JsonObject inv = check.getAsJsonArray("invariants").get(0).getAsJsonObject();
		assertEquals(6800, inv.get("reports").getAsLong());
		assertEquals(6799, check.getAsJsonObject("untraced_reports").get("Inv").getAsLong());
		assertTrue("reports past the cap were kept as messages: " + messages, messages < 200);
		h.resident.shutdown();
	}
}
