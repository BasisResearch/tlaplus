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

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

/**
 * Under continuation TLC checks no further invariant on a state once one
 * fails there. InvB fails exactly where InvA does, so TLC never reports it;
 * the resident must still find it violated, over the store, and the
 * registers must say the exhausted run found violations.
 */
public class ResidentContinuationInvariantsTest {

	static final String SPEC = "---- MODULE CI ----\n" //
			+ "EXTENDS Naturals\n" //
			+ "VARIABLE x\n" //
			+ "Init == x = 0\n" //
			+ "Next == x < 5 /\\ x' = x + 1\n" //
			+ "InvA == x # 3\n" //
			+ "InvB == x # 3\n" //
			+ "InvC == x < 10\n" //
			+ "====\n";
	static final String CFG = "INIT Init\nNEXT Next\nINVARIANT InvA\nINVARIANT InvB\nINVARIANT InvC\n";

	static JsonObject verdict(final JsonObject check, final String name) {
		final JsonArray invs = check.getAsJsonArray("invariants");
		for (int i = 0; i < invs.size(); i++) {
			final JsonObject v = invs.get(i).getAsJsonObject();
			if (name.equals(v.get("name").getAsString())) {
				return v;
			}
		}
		throw new AssertionError("no verdict for " + name + " in " + check);
	}

	@Test
	public void testSkippedInvariantIsSwept() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("CI.cfg", CFG);
		h.write("CI.tla", SPEC);
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("CI") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\",\"continue\":true}");
		assertEquals(check.toString(), "violated", verdict(check, "InvA").get("verdict").getAsString());
		final JsonObject b = verdict(check, "InvB");
		assertEquals(check.toString(), "violated", b.get("verdict").getAsString());
		assertEquals(1, b.get("reports").getAsLong());
		assertEquals(4, b.get("level").getAsInt());
		assertEquals("store", b.get("source").getAsString());
		assertEquals(check.toString(), "no_violation_found", verdict(check, "InvC").get("verdict").getAsString());

		final JsonObject registers = h.ok("{\"command\":\"registers\"}").getAsJsonObject("registers");
		assertEquals(registers.toString(), "exhausted_with_violations", registers.get("stopped_by").getAsString());
		h.resident.shutdown();
	}
}
