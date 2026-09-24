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

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * Under continuation every initial state that violates an invariant is
 * listed with its state, those a state constraint excludes included, next to
 * the traces of violations reached later.
 */
public class ResidentInitialViolationContinueTest {

	@Test
	public void testInitialViolationsAreListed() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("IC.cfg", "INIT Init\nNEXT Next\nINVARIANT Small\nCONSTRAINT Bound\n");
		h.write("IC.tla", "---- MODULE IC ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "Init == x \\in {0, 9, 20}\n" //
				+ "Next == x < 9 /\\ x' = x + 1\n" //
				+ "Small == x < 8\n" //
				+ "Bound == x < 15\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("IC") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\",\"continue\":true}");
		assertTrue(check.toString(), check.get("finished").getAsBoolean());
		final Set<Integer> initial = new HashSet<>();
		int behaviours = 0;
		for (final JsonElement e : check.getAsJsonArray("traces")) {
			final JsonObject t = e.getAsJsonObject();
			if (t.get("length").getAsInt() == 1) {
				final JsonObject s = t.getAsJsonArray("states").get(0).getAsJsonObject();
				assertEquals(check.toString(), "<Initial predicate>", s.get("action").getAsString());
				initial.add(s.getAsJsonObject("vars").get("x").getAsInt());
			} else {
				behaviours++;
			}
		}
		// 9 is in the model, 20 excluded by the constraint; 8 is reached from 0.
		assertEquals(check.toString(), Set.of(9, 20), initial);
		assertEquals(check.toString(), 1, behaviours);
		final JsonObject small = check.getAsJsonArray("invariants").get(0).getAsJsonObject();
		assertEquals(check.toString(), "violated", small.get("verdict").getAsString());
		assertEquals(check.toString(), 1, small.get("level").getAsInt());
		h.resident.shutdown();
	}
}
