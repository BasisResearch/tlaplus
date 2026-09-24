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
 * TLC checks invariants on successors a state constraint excludes. A refresh
 * must too: an invariant that fails only on the excluded state is violated
 * in the refreshed graph, as a fresh run reports.
 */
public class ResidentRefreshExcludedTest {

	private static String spec(final int bad) {
		return "---- MODULE RX ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "Init == x = 0\n" //
				+ "Next == x' = x + 1\n" //
				+ "Inv == x # " + bad + "\n" //
				+ "Cons == x < 3\n" //
				+ "====\n";
	}

	@Test
	public void testExcludedSuccessorIsChecked() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("RX.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTRAINT Cons\n");
		h.write("RX.tla", spec(7));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("RX") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals(check.toString(), "no_violation_found", verdict(check, "Inv").get("verdict").getAsString());
		// 0, 1 and 2 are in the model; 3 is excluded and kept.
		assertEquals(check.toString(), 3, check.getAsJsonObject("stats").getAsJsonObject("store").get("states").getAsLong());
		assertEquals(check.toString(), 1,
				check.getAsJsonObject("stats").getAsJsonObject("store").get("excluded_states").getAsLong());

		// Only the excluded state violates the edited invariant.
		h.write("RX.tla", spec(3));
		final JsonObject refresh = h.ok("{\"command\":\"refresh\"}");
		assertEquals(refresh.toString(), "incremental", refresh.get("mode").getAsString());
		final JsonObject inv = verdict(refresh, "Inv");
		assertEquals(refresh.toString(), "violated", inv.get("verdict").getAsString());
		assertEquals(refresh.toString(), 4, inv.get("level").getAsInt());
		assertEquals(refresh.toString(), 1, refresh.getAsJsonArray("violations").size());
		// The path to the excluded state is served like any other.
		final JsonObject trace = h.ok("{\"command\":\"trace\",\"fp\":\"" + inv.get("fp").getAsString() + "\"}");
		assertEquals(trace.toString(), 4, trace.get("length").getAsInt());

		// The excluded edge was carried: a further edit replays it again.
		h.write("RX.tla", spec(2));
		final JsonObject again = h.ok("{\"command\":\"refresh\"}");
		assertEquals(again.toString(), "violated", verdict(again, "Inv").get("verdict").getAsString());
		assertEquals(again.toString(), 3, verdict(again, "Inv").get("level").getAsInt());

		// And an added action that generates the excluded state anew.
		h.write("RX.tla", spec(3).replace("Next == x' = x + 1", "Next == x' = x + 1 \\/ x' = x + 2"));
		final JsonObject added = h.ok("{\"command\":\"refresh\",\"continue\":true}");
		assertEquals(added.toString(), "violated", verdict(added, "Inv").get("verdict").getAsString());
		h.resident.shutdown();
	}
}
