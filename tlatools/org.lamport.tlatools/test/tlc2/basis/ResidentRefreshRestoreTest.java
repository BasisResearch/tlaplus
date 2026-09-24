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

/**
 * A refresh whose edited spec declares a variable named like one of the old
 * spec's definitions is not adopted; the old spec's name slots are put back,
 * so the session still evaluates the definition as a definition.
 */
public class ResidentRefreshRestoreTest {

	@Test
	public void testDefinitionBecomesVariable() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("RR.cfg", "INIT Init\nNEXT Next\n");
		h.write("RR.tla", "---- MODULE RR ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "y == 5\n" //
				+ "Init == x = 0\n" //
				+ "Next == x < 2 /\\ x' = x + 1\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("RR") + "\",\"workers\":1,\"deadlock\":false}");
		h.ok("{\"command\":\"check\"}");
		final String screen = "{\"command\":\"screen\",\"candidates\":[\"y = 5\",\"x + y > 4\"]}";
		assertHolds(h.ok(screen));

		h.write("RR.tla", "---- MODULE RR ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES x, y\n" //
				+ "Init == x = 0 /\\ y = 0\n" //
				+ "Next == x < 2 /\\ x' = x + 1 /\\ y' = y\n" //
				+ "====\n");
		final JsonObject refresh = h.ok("{\"command\":\"refresh\"}");
		assertTrue(refresh.toString(), refresh.get("restart_required").getAsBoolean());
		assertHolds(h.ok(screen));
		h.resident.shutdown();
	}

	private static void assertHolds(final JsonObject screen) {
		for (int i = 0; i < 2; i++) {
			assertEquals(screen.toString(), "holds_on_stored",
					screen.getAsJsonArray("results").get(i).getAsJsonObject().get("verdict").getAsString());
		}
	}
}
