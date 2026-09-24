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

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

/**
 * An invariant that fails to evaluate is not violated: its verdict says it
 * could not be evaluated, and the run that stopped on the error did not
 * explore the whole graph. Under continuation TLC prints the failing
 * behaviour a second time when it rebuilds the call stack; the trace holds
 * it once.
 */
public class ResidentEvaluationFailedContinueTest {

	@Test
	public void testEvaluationFailure() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("E.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("E.tla", "---- MODULE E ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "Init == x = 0\n" //
				+ "Next == x < 5 /\\ x' = x + 1\n" //
				+ "Inv == IF x = 3 THEN (1 \\div 0) = 1 ELSE TRUE\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("E") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\",\"continue\":true}");
		assertTrue(check.toString(), check.get("finished").getAsBoolean());
		assertEquals(check.toString(), "evaluation_failed", check.get("verdict").getAsString());

		final JsonArray invariants = check.getAsJsonArray("invariants");
		assertEquals(1, invariants.size());
		final JsonObject inv = invariants.get(0).getAsJsonObject();
		assertEquals(inv.toString(), "not_evaluable", inv.get("verdict").getAsString());
		assertFalse(inv.toString(), inv.has("reports"));
		assertTrue(inv.toString(), inv.has("error"));
		// x = 3 is the fourth state of the behaviour.
		assertEquals(inv.toString(), 4, inv.get("level").getAsInt());

		final JsonObject trace = check.getAsJsonObject("trace");
		assertEquals(trace.toString(), 4, trace.get("length").getAsInt());
		final JsonArray states = trace.getAsJsonArray("states");
		for (int i = 0; i < states.size(); i++) {
			assertEquals(states.toString(), i + 1, states.get(i).getAsJsonObject().get("ordinal").getAsInt());
		}

		// x = 4 and x = 5 were never explored.
		final JsonObject registers = h.ok("{\"command\":\"registers\"}").getAsJsonObject("registers");
		assertFalse(registers.toString(), registers.get("exhausted").getAsBoolean());
		assertEquals(registers.toString(), "error", registers.get("stopped_by").getAsString());
		h.resident.shutdown();
	}
}
