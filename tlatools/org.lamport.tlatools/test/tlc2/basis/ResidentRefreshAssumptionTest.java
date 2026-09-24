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
import static tlc2.basis.ResidentHarness.storeStates;

import org.junit.Test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

/**
 * A refresh checks what TLC checks before and at the initial states: an
 * edited ASSUME that is false leaves the edit unadopted (TLC would explore
 * nothing), and a state-level PROPERTY, which TLC checks on the initial
 * states only, gets a verdict over the stored initial states.
 */
public class ResidentRefreshAssumptionTest {

	private static String spec(final String assume, final String pos, final int lim) {
		return "---- MODULE A ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "CONSTANT N\n" //
				+ "VARIABLE x\n" //
				+ "ASSUME " + assume + "\n" //
				+ "Init == x = 0\n" //
				+ "Inc == x < " + lim + " /\\ x' = x + 1\n" //
				+ "Dec == x > 0 /\\ x' = x - 1\n" //
				+ "Next == Inc \\/ Dec\n" //
				+ "TypeOK == x \\in 0..N\n" //
				+ "Pos == " + pos + "\n" //
				+ "====\n";
	}

	private static JsonObject named(final JsonArray verdicts, final String name) {
		for (int i = 0; i < verdicts.size(); i++) {
			final JsonObject v = verdicts.get(i).getAsJsonObject();
			if (name.equals(v.get("name").getAsString())) {
				return v;
			}
		}
		throw new AssertionError("no verdict for " + name + " in " + verdicts);
	}

	@Test
	public void testAssumptionsAndImpliedInits() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("A.cfg", "CONSTANT N = 3\nINIT Init\nNEXT Next\nINVARIANT TypeOK\nPROPERTY Pos\n");
		h.write("A.tla", spec("N > 0", "x >= 0", 3));
		final JsonObject open = h
				.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("A") + "\",\"workers\":1,\"deadlock\":false}");
		assertTrue(open.toString(), open.getAsJsonObject("catalogue").getAsJsonArray("implied_inits").toString()
				.contains("Pos"));
		assertEquals("ok", h.ok("{\"command\":\"check\"}").get("verdict").getAsString());

		// A false assumption: not adopted, the store stays, and it still serves.
		h.write("A.tla", spec("N > 100", "x >= 0", 2));
		JsonObject r = h.ok("{\"command\":\"refresh\"}");
		assertFalse(r.toString(), r.get("adopted").getAsBoolean());
		assertEquals(r.toString(), "assumption_false", r.get("verdict").getAsString());
		assertEquals(4, storeStates(r));
		final JsonObject screen = h.ok("{\"command\":\"screen\",\"candidates\":[\"x < 3\"]}");
		assertEquals("violated",
				screen.getAsJsonArray("results").get(0).getAsJsonObject().get("verdict").getAsString());

		// The assumption fixed and the state-level property broken: adopted,
		// and the property is violated in the initial state, as TLC reports it.
		h.write("A.tla", spec("N > 0", "x >= 1", 2));
		r = h.ok("{\"command\":\"refresh\"}");
		assertEquals(r.toString(), "incremental", r.get("mode").getAsString());
		assertTrue(r.toString(), r.get("adopted").getAsBoolean());
		assertEquals("hold", r.get("assumptions").getAsString());
		assertEquals(3, storeStates(r));
		assertEquals(r.toString(), "violated_initially",
				named(r.getAsJsonArray("implied_inits"), "Pos").get("verdict").getAsString());
		assertEquals("no_violation_found", named(r.getAsJsonArray("invariants"), "TypeOK").get("verdict").getAsString());

		// And fixed again.
		h.write("A.tla", spec("N > 0", "x >= 0", 2));
		r = h.ok("{\"command\":\"refresh\"}");
		assertTrue(r.toString(), r.get("adopted").getAsBoolean());
		assertEquals("no_violation_found",
				named(r.getAsJsonArray("implied_inits"), "Pos").get("verdict").getAsString());
		h.resident.shutdown();
	}
}
