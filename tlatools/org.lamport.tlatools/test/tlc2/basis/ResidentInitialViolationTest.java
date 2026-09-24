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

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * An invariant false in an initial state has a one-state counterexample: TLC
 * prints that state only into its report, and the resident hands it on as a
 * typed state from the store, at level 1.
 */
public class ResidentInitialViolationTest {

	@Test
	public void testInitialInvariantViolationHasItsState() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("IV.cfg", "INIT Init\nNEXT Next\nINVARIANT Small\n");
		h.write("IV.tla", "---- MODULE IV ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "Init == x \\in {0, 9}\n" //
				+ "Next == x < 9 /\\ x' = x + 1\n" //
				+ "Small == x < 8\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("IV") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals(check.toString(), "invariant_violated", check.get("verdict").getAsString());
		final JsonObject trace = check.getAsJsonObject("trace");
		assertEquals(check.toString(), 1, trace.get("length").getAsInt());
		final JsonObject state = trace.getAsJsonArray("states").get(0).getAsJsonObject();
		assertEquals(check.toString(), 9, state.getAsJsonObject("vars").get("x").getAsInt());
		assertEquals(check.toString(), "<Initial predicate>", state.get("action").getAsString());
		assertEquals(check.toString(), 1, check.getAsJsonArray("traces").size());
		final JsonObject small = check.getAsJsonArray("invariants").get(0).getAsJsonObject();
		assertEquals(check.toString(), "violated", small.get("verdict").getAsString());
		assertEquals(check.toString(), 1, small.get("level").getAsInt());
		assertEquals(check.toString(), "<Initial predicate>", small.get("action").getAsString());
		h.resident.shutdown();
	}
}
