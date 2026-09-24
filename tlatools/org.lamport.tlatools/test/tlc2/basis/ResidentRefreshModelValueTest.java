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

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * Every parse resets TLC's model-value table, and a stored state names a
 * model value by its index there. A refresh that is not adopted must put
 * the old table back, or the store decodes against the edited spec's
 * numbering; an edit that renumbers the model values cannot be replayed at
 * all; one that only adds a model value after the others can.
 */
public class ResidentRefreshModelValueTest {

	private static String spec(final String values, final int bound, final boolean broken) {
		return "---- MODULE MV ----\n" //
				+ "EXTENDS Naturals, TLCExt\n" //
				+ "VARIABLE x\n" //
				+ values //
				+ "Init == x = NoVal\n" //
				+ "A == x = NoVal /\\ x' = 0\n" //
				+ "B == x \\in Nat /\\ x < " + bound + " /\\ x' = x + 1\n" //
				+ "Next == A \\/ B" + (broken ? " \\/ ((" : "") + "\n" //
				+ "Inv == x = NoVal \\/ x < 10\n" //
				+ "====\n";
	}

	private static final String NOVAL = "NoVal == TLCModelValue(\"NoVal\")\n";

	/** How many stored states are not NoVal, by screening the store. */
	private static long notNoVal(final ResidentHarness h) throws Exception {
		final JsonObject screen = h.ok("{\"command\":\"screen\",\"candidates\":[\"x = NoVal\"]}");
		final JsonObject result = screen.getAsJsonArray("results").get(0).getAsJsonObject();
		assertEquals(result.toString(), "violated", result.get("verdict").getAsString());
		return result.get("violations").getAsLong();
	}

	@Test
	public void testModelValuesSurviveRefreshes() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("MV.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("MV.tla", spec(NOVAL, 3, false));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("MV") + "\",\"workers\":1,\"deadlock\":false}");
		assertEquals("ok", h.ok("{\"command\":\"check\"}").get("verdict").getAsString());
		assertEquals(4, notNoVal(h));

		// A parse failure: the parse reset the table before it failed.
		h.write("MV.tla", spec(NOVAL, 3, true));
		final JsonObject failed = h.call("{\"command\":\"refresh\"}");
		assertEquals(failed.toString(), "parse_failed", failed.get("error_code").getAsString());
		assertEquals(4, notNoVal(h));

		// A model value ahead of NoVal takes its index: nothing can be carried.
		h.write("MV.tla", spec("Aaa == TLCModelValue(\"Aaa\")\n" + NOVAL, 3, false));
		final JsonObject renumbered = h.ok("{\"command\":\"refresh\"}");
		assertEquals(renumbered.toString(), "full", renumbered.get("mode").getAsString());
		assertTrue(renumbered.toString(), renumbered.get("restart_required").getAsBoolean());
		assertTrue(renumbered.toString(), renumbered.get("reason").getAsString().contains("model values"));
		assertEquals(4, notNoVal(h));

		// One added after NoVal keeps every stored index: replayed as usual.
		h.write("MV.tla", spec(NOVAL + "Zzz == TLCModelValue(\"Zzz\")\n", 4, false));
		final JsonObject appended = h.ok("{\"command\":\"refresh\"}");
		assertEquals(appended.toString(), "incremental", appended.get("mode").getAsString());
		assertTrue(appended.toString(), appended.get("adopted").getAsBoolean());
		assertFalse(appended.toString(), appended.has("restart_required"));
		assertEquals(6, appended.getAsJsonObject("store").get("states").getAsLong());
		assertEquals(5, notNoVal(h));
		h.resident.shutdown();
	}
}
