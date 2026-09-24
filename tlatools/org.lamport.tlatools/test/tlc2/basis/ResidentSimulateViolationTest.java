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

/** A simulation that reaches an invariant violation reports it with its behaviour. */
public class ResidentSimulateViolationTest {

	@Test
	public void testViolationIsReported() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("SV.cfg", "INIT Init\nNEXT Next\nINVARIANT Small\n");
		h.write("SV.tla", "---- MODULE SV ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "Init == x = 0\n" //
				+ "Next == x' = x + 1\n" //
				+ "Small == x < 3\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("SV")
				+ "\",\"mode\":\"simulate\",\"workers\":1,\"depth\":10,\"traces\":5,\"seed\":1}");
		final JsonObject sim = h.ok("{\"command\":\"simulate\",\"budget_ms\":30000}");
		assertTrue(sim.toString(), sim.get("finished").getAsBoolean());
		assertEquals(sim.toString(), "invariant_violated", sim.get("verdict").getAsString());
		assertEquals(sim.toString(), "Small", sim.get("violated").getAsString());
		assertEquals(sim.toString(), 4, sim.getAsJsonObject("trace").get("length").getAsInt());
		h.resident.shutdown();
	}
}
