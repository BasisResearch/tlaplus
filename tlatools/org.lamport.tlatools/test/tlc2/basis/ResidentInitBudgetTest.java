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
 * A budget that runs out while the initial states are generated, in a run
 * that then ends there (an initial state violates the invariant): no worker
 * ever starts, and the budget's suspend must not wait for one.
 */
public class ResidentInitBudgetTest {

	@Test(timeout = 120_000)
	public void testBudgetDuringInit() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("I.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("I.tla", "---- MODULE I ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES x\n" //
				+ "Init == x \\in 1..400000\n" //
				+ "Next == x' = x\n" //
				+ "Inv == x < 390000\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("I") + "\",\"workers\":2}");
		// Returns rather than hanging, whether or not the run has ended yet.
		h.ok("{\"command\":\"check\",\"budget_ms\":1}");
		final JsonObject done = h.ok("{\"command\":\"check\"}");
		assertTrue(done.toString(), done.get("finished").getAsBoolean());
		assertEquals(done.toString(), "invariant_violated", done.get("verdict").getAsString());
		h.resident.shutdown();
	}
}
