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

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * A PROPERTY that is false in an initial state is a violation, named as
 * such, not an error.
 */
public class ResidentPropertyInitialTest {

	@Test
	public void testInitialPropertyViolation() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("PI.cfg", "INIT Init\nNEXT Next\nPROPERTY Prop\n");
		h.write("PI.tla", "---- MODULE PI ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "Init == x = 0\n" //
				+ "Next == x < 2 /\\ x' = x + 1\n" //
				+ "Prop == x = 1\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("PI") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals(check.toString(), "property_violated", check.get("verdict").getAsString());
		assertEquals(check.toString(), "Prop", check.get("violated").getAsString());
		// TLC prints the state only into its report; the trace carries it.
		final JsonObject trace = check.getAsJsonObject("trace");
		assertEquals(check.toString(), 1, trace.get("length").getAsInt());
		assertEquals(check.toString(), 0, trace.getAsJsonArray("states").get(0).getAsJsonObject()
				.getAsJsonObject("vars").get("x").getAsInt());
		final JsonObject registers = h.ok("{\"command\":\"registers\"}").getAsJsonObject("registers");
		assertFalse(registers.get("exhausted").getAsBoolean());
		assertEquals(registers.toString(), "violation", registers.get("stopped_by").getAsString());
		h.resident.shutdown();
	}
}
