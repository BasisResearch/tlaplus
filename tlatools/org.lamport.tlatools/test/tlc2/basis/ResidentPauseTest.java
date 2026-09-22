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

import tlc2.TLCGlobals;

/**
 * A budget pause must hold while TLC does its periodic work. With a
 * checkpoint due on every wake-up, each suspend wakes the checker's main
 * thread into a checkpoint, which suspends and resumes the queue on its own;
 * that resume must not restart workers the resident parked.
 */
public class ResidentPauseTest {

	@Test
	public void testPauseHoldsThroughCheckpoints() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("P.cfg", "INIT Init\nNEXT Next\n");
		h.write("P.tla", "---- MODULE P ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES a, b, c\n" //
				+ "N == 30\n" //
				+ "Init == a = 0 /\\ b = 0 /\\ c = 0\n" //
				+ "A == a < N-1 /\\ a' = a + 1 /\\ UNCHANGED <<b, c>>\n" //
				+ "B == b < N-1 /\\ b' = b + 1 /\\ UNCHANGED <<a, c>>\n" //
				+ "C == c < N-1 /\\ c' = c + 1 /\\ UNCHANGED <<a, b>>\n" //
				+ "Next == A \\/ B \\/ C\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("P") + "\",\"workers\":2,\"deadlock\":false,\"coverage\":false}");
		TLCGlobals.chkptDuration = 1;

		final JsonObject paused = h.ok("{\"command\":\"check\",\"budget_states\":50}");
		assertFalse(paused.get("finished").getAsBoolean());
		final long before = h.ok("{\"command\":\"stats\"}").getAsJsonObject("stats").get("distinct").getAsLong();
		for (int i = 0; i < 5; i++) {
			// Each suspend wakes the main thread into a checkpoint.
			h.ok("{\"command\":\"screen\",\"candidates\":[\"a < 100\"]}");
			Thread.sleep(300);
		}
		final JsonObject stats = h.ok("{\"command\":\"stats\"}").getAsJsonObject("stats");
		assertEquals("workers ran while paused", before, stats.get("distinct").getAsLong());
		assertTrue(stats.get("running").getAsBoolean());

		final JsonObject done = h.ok("{\"command\":\"check\"}");
		assertTrue(done.get("finished").getAsBoolean());
		assertEquals("ok", done.get("verdict").getAsString());
		assertEquals(27000, done.getAsJsonObject("stats").get("distinct").getAsLong());
		h.resident.shutdown();
	}
}
