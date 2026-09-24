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
 * A constraint that reads {@code TLCGet("level")} only through a definition
 * the config substitutes in ({@code CONSTANT Depth <- D}): the substitution
 * is bound as a tool object, so the syntactic walk from the constraint never
 * reaches {@code TLCGet}. The refresh must still ask for a full run; replayed
 * without a predecessor, the constraint excluded nothing and the replay ran
 * away.
 */
public class ResidentRefreshTLCGetSubstitutionTest {

	private static String spec(final String next) {
		return "---- MODULE S ----\n" //
				+ "EXTENDS Naturals, TLC\n" //
				+ "VARIABLES x\n" //
				+ "Depth == 0\n" //
				+ "D == TLCGet(\"level\")\n" //
				+ "Constr == Depth < 4\n" //
				+ "Init == x = 0\n" //
				+ "Inc == x' = x + 1\n" //
				+ "Jump == x' = x + 3\n" //
				+ "Next == " + next + "\n" //
				+ "Inv == TRUE\n" //
				+ "====\n";
	}

	@Test
	public void testSubstitutedLevelConstraint() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("S.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTRAINT Constr\nCONSTANT Depth <- D\n");
		h.write("S.tla", spec("Inc"));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("S") + "\",\"workers\":1,\"deadlock\":false}");
		assertEquals("ok", h.ok("{\"command\":\"check\"}").get("verdict").getAsString());
		h.write("S.tla", spec("Inc \\/ Jump"));
		final JsonObject r = h.ok("{\"command\":\"refresh\",\"budget_ms\":10000}");
		assertEquals(r.toString(), "full", r.get("mode").getAsString());
		assertTrue(r.toString(), r.get("restart_required").getAsBoolean());
		assertTrue(r.toString(), r.get("reason").getAsString().contains("Depth <- D"));
		h.resident.shutdown();
	}
}
