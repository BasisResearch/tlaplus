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
import static tlc2.basis.ResidentHarness.storeStates;

import java.io.File;

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * An edited invariant that does not evaluate on a state carried over from
 * the old graph: the refresh must answer as a replay that failed (not
 * adopted, with the error), keep serving the old store, release the new
 * one, and leave the next refresh working.
 */
public class ResidentRefreshInvariantErrorTest {

	private static String spec(final String inv) {
		return "---- MODULE E ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES x\n" //
				+ "Init == x = 0\n" //
				+ "Inc == x < 5 /\\ x' = x + 1\n" //
				+ "Next == Inc\n" //
				+ "Inv == " + inv + "\n" //
				+ "====\n";
	}

	private static int storeFiles(final ResidentHarness h) {
		int files = 0;
		final File[] metadirs = new File(h.dir.toFile(), "states").listFiles();
		for (final File metadir : metadirs == null ? new File[0] : metadirs) {
			if (new File(metadir, "basis.states").exists()) {
				files++;
			}
		}
		return files;
	}

	@Test
	public void testInvariantThatDoesNotEvaluate() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("E.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
		h.write("E.tla", spec("x <= 5"));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("E") + "\",\"workers\":1,\"deadlock\":false}");
		final JsonObject check = h.ok("{\"command\":\"check\"}");
		assertEquals("ok", check.get("verdict").getAsString());
		assertEquals(6, storeStates(check.getAsJsonObject("stats")));

		// Every stored state survives (no action changed), and the changed
		// invariant fails to evaluate on the first of them.
		final int filesBefore = storeFiles(h);
		h.write("E.tla", spec("x.foo <= 5"));
		JsonObject r = h.ok("{\"command\":\"refresh\"}");
		assertFalse(r.toString(), r.get("adopted").getAsBoolean());
		assertTrue(r.toString(), r.get("error").getAsString().contains("Inv"));
		assertEquals(6, storeStates(r));
		assertEquals("the unadopted store was not released", filesBefore, storeFiles(h));

		// The old spec is still what the store queries evaluate against...
		final long fp = h.ok("{\"command\":\"screen\",\"candidates\":[\"x < 1\"]}").getAsJsonArray("results").get(0)
				.getAsJsonObject().get("first_violation_fp").getAsLong();
		final JsonObject eval = h.ok("{\"command\":\"eval\",\"fp\":" + fp + ",\"expr\":\"x + 1\"}");
		assertTrue(eval.toString(), eval.get("evaluated").getAsBoolean());

		// ...and a fixed edit replays as usual.
		h.write("E.tla", spec("x <= 4"));
		r = h.ok("{\"command\":\"refresh\",\"continue\":true}");
		assertTrue(r.toString(), r.get("adopted").getAsBoolean());
		assertTrue(r.get("complete").getAsBoolean());
		assertEquals("violated", r.getAsJsonArray("invariants").get(0).getAsJsonObject().get("verdict").getAsString());
		h.resident.shutdown();
	}
}
