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
 * Under a SYMMETRY set a fingerprint names every permutation of a state, and
 * the store keeps the one TLC reached first, so a refresh asks for a full
 * rerun as it does under a VIEW.
 */
public class ResidentRefreshSymmetryTest {

	private static String spec(final boolean remove) {
		return "---- MODULE S ----\n" //
				+ "EXTENDS TLC\n" //
				+ "CONSTANT P\n" //
				+ "VARIABLE s\n" //
				+ "Init == s = {}\n" //
				+ "Add == \\E p \\in P : p \\notin s /\\ s' = s \\cup {p}\n" //
				+ (remove ? "Remove == \\E p \\in s : s' = s \\ {p}\n" : "") //
				+ "Next == Add" + (remove ? " \\/ Remove" : "") + "\n" //
				+ "Inv == s \\subseteq P\n" //
				+ "Perms == Permutations(P)\n" //
				+ "====\n";
	}

	@Test
	public void testSymmetryRefreshIsFullRerun() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("S.cfg", "CONSTANT P = {p1, p2}\nSYMMETRY Perms\nINIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("S.tla", spec(false));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("S") + "\",\"workers\":1,\"deadlock\":false}");
		assertEquals("ok", h.ok("{\"command\":\"check\"}").get("verdict").getAsString());

		h.write("S.tla", spec(true));
		final JsonObject r = h.ok("{\"command\":\"refresh\"}");
		assertEquals(r.toString(), "full", r.get("mode").getAsString());
		assertTrue(r.toString(), r.get("restart_required").getAsBoolean());
		assertTrue(r.toString(), r.get("reason").getAsString().contains("SYMMETRY"));
		h.resident.shutdown();
	}
}
