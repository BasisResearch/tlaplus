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
 * A run that stopped at its first violation did not explore the whole
 * graph, and asking for continuation after it ended must not make it look
 * as if it had: the next refresh must restart rather than replay a partial
 * graph.
 */
public class ResidentContinuationTest {

	private static String spec(final String inv) {
		return "---- MODULE K ----\n" //
				+ "EXTENDS Integers\n" //
				+ "VARIABLE x\n" //
				+ "Init == x = 0\n" //
				+ "A == x \\in 0..4 /\\ x' = x + 1\n" //
				+ "Next == A\n" //
				+ "Inv == " + inv + "\n" //
				+ "====\n";
	}

	@Test
	public void testContinuationAfterTheRunEnded() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("K.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("K.tla", spec("x < 3"));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("K") + "\",\"workers\":1,\"deadlock\":false}");
		JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals("invariant_violated", check.get("verdict").getAsString());
		assertFalse(check.get("continuation").getAsBoolean());

		// The run has ended; this explores nothing and changes nothing.
		check = h.ok("{\"command\":\"check\",\"continue\":true}");
		assertFalse(check.toString(), check.get("continuation").getAsBoolean());
		final JsonObject registers = h.ok("{\"command\":\"registers\"}").getAsJsonObject("registers");
		assertFalse(registers.toString(), registers.get("exhausted").getAsBoolean());
		assertEquals("violation", registers.get("stopped_by").getAsString());

		// x = 5 is reachable but was never generated: no replay can know.
		h.write("K.tla", spec("x /= 5"));
		final JsonObject r = h.ok("{\"command\":\"refresh\"}");
		assertEquals(r.toString(), "full", r.get("mode").getAsString());
		assertTrue(r.get("restart_required").getAsBoolean());
		h.resident.shutdown();
	}
}
