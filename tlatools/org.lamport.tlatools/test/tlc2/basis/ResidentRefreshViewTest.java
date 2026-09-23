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
 * Under a VIEW a refresh asks for a full rerun. Here x = 1 is first reached
 * with y = 1 by A, whose store content is (1, 1); B reaches it with y = 2.
 * Once A changes, (1, 1) is unreachable, yet a replay copying B's edge would
 * store it and carry D from it to x = 5, a state a fresh run never reaches.
 */
public class ResidentRefreshViewTest {

	private static String spec(final String ay) {
		return "---- MODULE V ----\n" //
				+ "VARIABLES x, y\n" //
				+ "Init == x = 0 /\\ y = 0\n" //
				+ "A == x = 0 /\\ x' = 1 /\\ y' = " + ay + "\n" //
				+ "B == x = 0 /\\ x' = 1 /\\ y' = 2\n" //
				+ "D == x = 1 /\\ y = 1 /\\ x' = 5 /\\ y' = 0\n" //
				+ "Next == A \\/ B \\/ D\n" //
				+ "Inv == x /= 7\n" //
				+ "View == x\n" //
				+ "====\n";
	}

	@Test
	public void testViewRefreshIsFullRerun() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("V.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW View\n");
		h.write("V.tla", spec("1"));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("V") + "\",\"workers\":1,\"deadlock\":false}");
		assertEquals("ok", h.ok("{\"command\":\"check\"}").get("verdict").getAsString());

		h.write("V.tla", spec("3"));
		final JsonObject r = h.ok("{\"command\":\"refresh\"}");
		assertEquals(r.toString(), "full", r.get("mode").getAsString());
		assertTrue(r.toString(), r.get("restart_required").getAsBoolean());
		assertTrue(r.toString(), r.get("reason").getAsString().contains("VIEW"));
		// Nothing was adopted: the old store still serves.
		h.ok("{\"command\":\"screen\",\"candidates\":[\"x /= 5\"]}");
		h.resident.shutdown();
	}
}
