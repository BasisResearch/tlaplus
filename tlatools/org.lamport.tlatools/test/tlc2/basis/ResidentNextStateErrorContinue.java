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

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * Under continuation TLC keeps going after the next-state relation fails to
 * evaluate, and with deadlock checking on it then reports the state whose
 * expansion the error aborted as a deadlock, which overwrites the error's
 * code. The run is still an error: B's successor of x = 2, which violates
 * Inv, was never generated, so Inv has no verdict and the store is not the
 * whole graph. The earlier violation of Inv2 keeps its own two-state trace
 * though the error's behaviour is printed after it. Shared by
 * {@link ResidentNextStateErrorContinueTest} (deadlock checked) and
 * {@link ResidentNextStateErrorContinueNoDeadlockTest}.
 */
final class ResidentNextStateErrorContinue {

	private static final String SPEC = "---- MODULE F ----\n" //
			+ "EXTENDS Naturals\n" //
			+ "VARIABLE x\n" //
			+ "Init == x = 0\n" //
			+ "A == x < 5 /\\ x' = IF x = 2 THEN 1 \\div 0 ELSE x + 1\n" //
			+ "B == x = 2 /\\ x' = 10\n" //
			+ "Next == A \\/ B\n" //
			+ "Inv == x < 10\n" //
			+ "Inv2 == x # 1\n" //
			+ "====\n";

	private ResidentNextStateErrorContinue() {
	}

	/** One resident per JVM: each deadlock setting runs in its own test class. */
	static void run(final boolean deadlock) throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("F.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\nINVARIANT Inv2\n");
		h.write("F.tla", SPEC);
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("F") + "\",\"workers\":1,\"deadlock\":" + deadlock + "}");
		final JsonObject check = h.ok("{\"command\":\"check\",\"continue\":true}");
		assertTrue(check.toString(), check.get("finished").getAsBoolean());
		assertEquals(check.toString(), "error", check.get("verdict").getAsString());
		assertTrue(check.toString(), check.has("error_code"));

		final JsonArray invariants = check.getAsJsonArray("invariants");
		final JsonObject inv = invariants.get(0).getAsJsonObject();
		assertEquals(inv.toString(), "Inv", inv.get("name").getAsString());
		assertEquals(inv.toString(), "not_evaluated", inv.get("verdict").getAsString());
		final JsonObject inv2 = invariants.get(1).getAsJsonObject();
		assertEquals(inv2.toString(), "violated", inv2.get("verdict").getAsString());
		// x = 1 is the second state of the behaviour.
		assertEquals(inv2.toString(), 2, inv2.get("level").getAsInt());

		JsonObject violation = null;
		for (final JsonElement t : check.getAsJsonArray("traces")) {
			final JsonElement property = t.getAsJsonObject().get("property");
			if (property != null && !property.isJsonNull() && "Inv2".equals(property.getAsString())) {
				violation = t.getAsJsonObject();
			}
		}
		assertTrue(check.toString(), violation != null);
		assertEquals(violation.toString(), 2, violation.get("length").getAsInt());

		final JsonObject registers = h.ok("{\"command\":\"registers\"}").getAsJsonObject("registers");
		assertFalse(registers.toString(), registers.get("exhausted").getAsBoolean());
		assertEquals(registers.toString(), "error", registers.get("stopped_by").getAsString());

		// Nothing to replay from: the store is not the whole graph.
		h.write("F.tla", SPEC.replace("Inv2 == x # 1", "Inv2 == x # 2"));
		final JsonObject refresh = h.ok("{\"command\":\"refresh\"}");
		assertEquals(refresh.toString(), "full", refresh.get("mode").getAsString());
		assertTrue(refresh.toString(), refresh.get("restart_required").getAsBoolean());
		h.resident.shutdown();
	}
}
