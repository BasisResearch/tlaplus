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
 * Without a store the states TLC skipped under continuation cannot be
 * revisited: an invariant TLC never reported gets no verdict either way.
 */
public class ResidentContinuationInvariantsNoStoreTest {

	@Test
	public void testSkippedInvariantIsNotEvaluated() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("CI.cfg", ResidentContinuationInvariantsTest.CFG);
		h.write("CI.tla", ResidentContinuationInvariantsTest.SPEC);
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("CI")
				+ "\",\"workers\":1,\"deadlock\":false,\"store\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\",\"continue\":true}");
		assertEquals(check.toString(), "violated",
				ResidentContinuationInvariantsTest.verdict(check, "InvA").get("verdict").getAsString());
		assertEquals(check.toString(), "not_evaluated",
				ResidentContinuationInvariantsTest.verdict(check, "InvB").get("verdict").getAsString());
		assertEquals(check.toString(), "not_evaluated",
				ResidentContinuationInvariantsTest.verdict(check, "InvC").get("verdict").getAsString());
		h.resident.shutdown();
	}
}
