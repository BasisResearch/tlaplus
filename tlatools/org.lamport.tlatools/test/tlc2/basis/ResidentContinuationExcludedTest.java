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
import static tlc2.basis.ResidentContinuationInvariantsTest.verdict;

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * Under continuation TLC stops checking invariants on a state at the first
 * one it violates, excluded successors included. The sweep that decides the
 * skipped invariants must reach the excluded successors as TLC does.
 */
public class ResidentContinuationExcludedTest {

	@Test
	public void testSkippedInvariantOnExcludedState() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("CX.cfg", "INIT Init\nNEXT Next\nINVARIANT InvA\nINVARIANT InvB\nCONSTRAINT Cons\n");
		h.write("CX.tla", "---- MODULE CX ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "Init == x = 0\n" //
				+ "Next == x' = x + 1\n" //
				+ "InvA == x < 2\n" //
				+ "InvB == x # 3\n" //
				+ "Cons == x < 3\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("CX") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\",\"continue\":true}");
		assertEquals(check.toString(), "violated", verdict(check, "InvA").get("verdict").getAsString());
		// x = 3 is excluded and fails InvA first, so TLC never checks InvB there.
		final JsonObject b = verdict(check, "InvB");
		assertEquals(check.toString(), "violated", b.get("verdict").getAsString());
		assertEquals(check.toString(), "store", b.get("source").getAsString());
		assertEquals(check.toString(), 4, b.get("level").getAsInt());
		h.resident.shutdown();
	}
}
