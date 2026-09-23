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
import static tlc2.basis.ResidentContinuationInvariantsTest.verdict;

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * A run paused under continuation after InvA was reported, then resumed
 * without it. TLC skipped InvB on the state where InvA failed while it
 * continued, so InvB's silence is still no verdict: the resident must sweep
 * it over the store, not call it clean because the last call did not continue.
 */
public class ResidentContinuationToggleTest {

	static final String SPEC = "---- MODULE CT ----\n" //
			+ "EXTENDS Naturals\n" //
			+ "VARIABLE x\n" //
			+ "Init == x = 0\n" //
			+ "Next == x < 40 /\\ x' = x + 1\n" //
			+ "InvA == x # 3\n" //
			+ "InvB == x # 3\n" //
			+ "====\n";
	static final String CFG = "INIT Init\nNEXT Next\nINVARIANT InvA\nINVARIANT InvB\n";

	@Test
	public void testResumeWithoutContinuationStillSweeps() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("CT.cfg", CFG);
		h.write("CT.tla", SPEC);
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("CT") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject paused = h.ok("{\"command\":\"check\",\"continue\":true,\"budget_states\":6}");
		assertFalse(paused.toString(), paused.get("finished").getAsBoolean());
		assertEquals(paused.toString(), "violated", verdict(paused, "InvA").get("verdict").getAsString());

		final JsonObject done = h.ok("{\"command\":\"check\",\"continue\":false}");
		assertTrue(done.toString(), done.get("finished").getAsBoolean());
		assertEquals(done.toString(), "violated", verdict(done, "InvA").get("verdict").getAsString());
		final JsonObject b = verdict(done, "InvB");
		assertEquals(done.toString(), "violated", b.get("verdict").getAsString());
		assertEquals("store", b.get("source").getAsString());
		assertEquals(4, b.get("level").getAsInt());
		h.resident.shutdown();
	}
}
