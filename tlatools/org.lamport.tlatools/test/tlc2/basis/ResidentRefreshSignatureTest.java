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
 * An action's signature must change when what it means changes, even where
 * no definition's body text does: swapping a definition's formal parameters,
 * or which parameter an INSTANCE substitution replaces.
 */
public class ResidentRefreshSignatureTest {

	private static String spec(final String params, final String with) {
		return "---- MODULE S ----\n" //
				+ "EXTENDS Integers\n" //
				+ "VARIABLES x, y\n" //
				+ "F(" + params + ") == a - b\n" //
				+ "I == INSTANCE SM WITH " + with + "\n" //
				+ "Init == x = 0 /\\ y = 0\n" //
				+ "A == x \\in 0..4 /\\ x' = x + F(2, 1) /\\ y' = y\n" //
				+ "B == y \\in 0..4 /\\ y' = y + I!D /\\ x' = x\n" //
				+ "Next == A \\/ B\n" //
				+ "Inv == x >= 0 /\\ y >= 0\n" //
				+ "====\n";
	}

	private static void assertChanged(final JsonObject r, final String changed, final String unchanged) {
		final JsonObject diff = r.getAsJsonObject("diff");
		assertEquals(r.toString(), "incremental", r.get("mode").getAsString());
		assertEquals(r.toString(), "[\"" + changed + "\"]", diff.getAsJsonArray("changed").toString());
		assertEquals(r.toString(), "[\"" + unchanged + "\"]", diff.getAsJsonArray("unchanged").toString());
		// A fresh run of the edit steps to -1, below Inv.
		assertEquals(r.toString(), "violated",
				r.getAsJsonArray("invariants").get(0).getAsJsonObject().get("verdict").getAsString());
	}

	@Test
	public void testSignature() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("S.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("SM.tla", "---- MODULE SM ----\nEXTENDS Integers\nCONSTANTS a, b\nD == a - b\n====\n");
		h.write("S.tla", spec("a, b", "a <- 2, b <- 1"));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("S") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals("ok", check.get("verdict").getAsString());
		assertEquals(36, ResidentHarness.storeStates(check.getAsJsonObject("stats")));

		// The same body text, the parameters swapped.
		h.write("S.tla", spec("b, a", "a <- 2, b <- 1"));
		assertChanged(h.ok("{\"command\":\"refresh\"}"), "A", "B");

		// The same expressions, substituted for the other parameters. The
		// replay above stopped at its violation, so this one diffs against
		// the complete original graph.
		h.write("S.tla", spec("a, b", "a <- 1, b <- 2"));
		final JsonObject r = h.ok("{\"command\":\"refresh\"}");
		assertChanged(r, "B", "A");
		assertEquals("last_complete", r.get("replayed_from").getAsString());

		// Moving the text without changing it is no edit.
		h.write("S.tla", spec("a, b", "a <- 2, b <- 1").replace("EXTENDS Integers\n", "EXTENDS Integers\n\n\n"));
		final JsonObject moved = h.ok("{\"command\":\"refresh\"}");
		assertEquals(moved.toString(), 0, moved.getAsJsonObject("diff").getAsJsonArray("changed").size());
		assertTrue(moved.toString(), moved.get("complete").getAsBoolean());
		assertEquals(36, ResidentHarness.storeStates(moved));
		h.resident.shutdown();
	}
}
