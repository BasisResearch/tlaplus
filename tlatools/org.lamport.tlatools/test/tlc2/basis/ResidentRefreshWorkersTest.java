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
import static tlc2.basis.ResidentHarness.storeEdges;
import static tlc2.basis.ResidentHarness.storeStates;

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * The store and its incremental refresh with several workers writing it
 * concurrently: each replay must hold what a fresh run stores. With b the
 * bound on y, a fresh run reaches 21(b+1) states over 42b+21 edges.
 */
public class ResidentRefreshWorkersTest {

	private static String spec(final int b) {
		return "---- MODULE W ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES x, y\n" //
				+ "Lim == 20\n" //
				+ "Init == x = 0 /\\ y = 0\n" //
				+ "Inc == x < Lim /\\ x' = x + 1 /\\ y' = y\n" //
				+ "Bump == y < " + b + " /\\ y' = y + 1 /\\ x' = x\n" //
				+ "Reset == x = Lim /\\ x' = 0 /\\ y' = y\n" //
				+ "Next == Inc \\/ Bump \\/ Reset\n" //
				+ "Inv == x + y < 1000\n" //
				+ "====\n";
	}

	@Test(timeout = 120_000)
	public void testRefreshWithWorkers() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("W.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("W.tla", spec(10));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("W") + "\",\"workers\":4,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals("ok", check.get("verdict").getAsString());
		assertEquals(231, storeStates(check.getAsJsonObject("stats")));
		assertEquals(441, storeEdges(check.getAsJsonObject("stats")));

		for (final int b : new int[] { 15, 7, 12 }) {
			h.write("W.tla", spec(b));
			final JsonObject r = h.ok("{\"command\":\"refresh\"}");
			assertEquals(r.toString(), "incremental", r.get("mode").getAsString());
			assertTrue(r.toString(), r.get("complete").getAsBoolean());
			assertEquals(r.toString(), 21 * (b + 1), storeStates(r));
			assertEquals(r.toString(), 42 * b + 21, storeEdges(r));
		}
		h.resident.shutdown();
	}
}
