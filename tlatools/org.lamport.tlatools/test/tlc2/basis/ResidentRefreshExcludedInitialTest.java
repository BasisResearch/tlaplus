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

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

/**
 * An initial state a state constraint excludes is never explored, but TLC
 * checks every invariant and state-level PROPERTY on it. The store keeps it,
 * so a refresh that edits an invariant or property violated only there
 * reports the violation, and later refreshes still carry it.
 */
public class ResidentRefreshExcludedInitialTest {

	private static String spec(final String inv, final String pos) {
		return "---- MODULE I ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "Init == x \\in {0, 10}\n" //
				+ "Next == x < 5 /\\ x' = x + 1\n" //
				+ "Bound == x < 5\n" //
				+ "Inv == " + inv + "\n" //
				+ "Pos == " + pos + "\n" //
				+ "====\n";
	}

	private static JsonObject first(final JsonArray verdicts) {
		assertEquals(verdicts.toString(), 1, verdicts.size());
		return verdicts.get(0).getAsJsonObject();
	}

	private static JsonObject refresh(final ResidentHarness h) throws Exception {
		// Past violations, so the replay covers the whole graph and the next
		// refresh replays from it.
		final JsonObject r = h.ok("{\"command\":\"refresh\",\"continue\":true}");
		assertEquals(r.toString(), "incremental", r.get("mode").getAsString());
		assertTrue(r.toString(), r.get("complete").getAsBoolean());
		return r;
	}

	@Test
	public void testExcludedInitialStates() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("I.cfg", "INIT Init\nNEXT Next\nCONSTRAINT Bound\nINVARIANT Inv\nPROPERTY Pos\n");
		h.write("I.tla", spec("x >= 0", "x >= 0"));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("I") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals(check.toString(), "ok", check.get("verdict").getAsString());

		// Violated only by x = 10, which the constraint excludes.
		h.write("I.tla", spec("x < 10", "x < 10"));
		JsonObject r = refresh(h);
		JsonObject inv = first(r.getAsJsonArray("invariants"));
		assertEquals(r.toString(), "violated", inv.get("verdict").getAsString());
		assertEquals(r.toString(), 1, inv.get("level").getAsInt());
		final long fp = inv.get("fp").getAsLong();
		assertEquals(r.toString(), "violated_initially",
				first(r.getAsJsonArray("implied_inits")).get("verdict").getAsString());
		final JsonObject trace = h.ok("{\"command\":\"trace\",\"fp\":\"" + fp + "\"}");
		assertEquals(trace.toString(), 1, trace.get("length").getAsInt());

		// Carried through a refresh from the refreshed store.
		h.write("I.tla", spec("x < 11", "x < 11"));
		r = refresh(h);
		assertEquals(r.toString(), "no_violation_found",
				first(r.getAsJsonArray("invariants")).get("verdict").getAsString());
		h.write("I.tla", spec("x /= 10", "x /= 10"));
		r = refresh(h);
		inv = first(r.getAsJsonArray("invariants"));
		assertEquals(r.toString(), "violated", inv.get("verdict").getAsString());
		assertEquals(r.toString(), fp, inv.get("fp").getAsLong());
		assertEquals(r.toString(), "violated_initially",
				first(r.getAsJsonArray("implied_inits")).get("verdict").getAsString());
		h.resident.shutdown();
	}
}
