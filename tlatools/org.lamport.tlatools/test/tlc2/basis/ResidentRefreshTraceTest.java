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
 * An invariant that reads the behaviour so far ({@code TLCExt!Trace}, which
 * TLC overrides in Java to walk the predecessor chain): its value depends on
 * the path to a state, which a replay neither preserves nor sets, so a
 * refresh asks for a full run.
 */
public class ResidentRefreshTraceTest {

	private static String spec(final int step) {
		return "---- MODULE T ----\n" //
				+ "EXTENDS Naturals, Sequences, TLCExt\n" //
				+ "VARIABLES x\n" //
				+ "Init == x = 0\n" //
				+ "Inc == x < 5 /\\ x' = x + " + step + "\n" //
				+ "Next == Inc\n" //
				+ "Inv == Len(Trace) < 100\n" //
				+ "====\n";
	}

	@Test
	public void testTraceInvariant() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("T.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("T.tla", spec(1));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("T") + "\",\"workers\":1,\"deadlock\":false}");
		assertEquals("ok", h.ok("{\"command\":\"check\"}").get("verdict").getAsString());
		h.write("T.tla", spec(2));
		final JsonObject r = h.ok("{\"command\":\"refresh\",\"budget_ms\":10000}");
		assertEquals(r.toString(), "full", r.get("mode").getAsString());
		assertTrue(r.toString(), r.get("restart_required").getAsBoolean());
		h.resident.shutdown();
	}
}
