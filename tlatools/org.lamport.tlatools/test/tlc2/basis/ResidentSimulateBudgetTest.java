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

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * A budget stop ends the simulator for good: the reply says it stopped on
 * its budget with nothing found, and a later call reports that run again as
 * not resumable instead of as a completed one.
 */
public class ResidentSimulateBudgetTest {

	@Test
	public void testBudgetStopIsFinal() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("SB.cfg", "INIT Init\nNEXT Next\nINVARIANT Ok\n");
		h.write("SB.tla", "---- MODULE SB ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "Init == x = 0\n" //
				+ "Next == x' = 1 - x\n" //
				+ "Ok == x \\in {0, 1}\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("SB")
				+ "\",\"mode\":\"simulate\",\"workers\":1,\"depth\":10,\"seed\":1}");
		final JsonObject first = h.ok("{\"command\":\"simulate\",\"budget_ms\":300}");
		assertTrue(first.toString(), first.get("stopped_by_budget").getAsBoolean());
		assertEquals(first.toString(), "no_violation_found", first.get("verdict").getAsString());
		final JsonObject again = h.ok("{\"command\":\"simulate\",\"budget_ms\":300}");
		assertFalse(again.toString(), again.get("resumable").getAsBoolean());
		assertTrue(again.toString(), again.get("stopped_by_budget").getAsBoolean());
		assertEquals(again.toString(), "no_violation_found", again.get("verdict").getAsString());
		h.resident.shutdown();
	}
}
