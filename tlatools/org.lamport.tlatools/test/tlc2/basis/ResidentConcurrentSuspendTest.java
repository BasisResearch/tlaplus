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

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import org.junit.Test;

import com.google.gson.JsonObject;

import tlc2.tool.ModelChecker;

/**
 * The resident's pause and TLC's periodic work (a liveness check or a
 * checkpoint) can both wait for the workers to park at once. The queue
 * wakes a single waiter when the last worker parks, so both must not wait
 * there together: with every state's expansion slow, the two start waiting
 * while workers are mid-expansion, and both must return.
 */
public class ResidentConcurrentSuspendTest {

	@Test(timeout = 120_000)
	public void testPauseAndPeriodicWorkSuspendTogether() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("S.cfg", "INIT Init\nNEXT Next\n");
		h.write("S.tla", "---- MODULE S ----\n" //
				+ "EXTENDS Naturals, FiniteSets\n" //
				+ "VARIABLES x, y\n" //
				+ "Heavy == Cardinality({s \\in SUBSET (1..16) : 1 \\in s}) > x\n" //
				+ "Init == x = 0 /\\ y = 0\n" //
				+ "A == Heavy /\\ x < 4 /\\ x' = x + 1 /\\ UNCHANGED y\n" //
				+ "B == Heavy /\\ y < 4 /\\ y' = y + 1 /\\ UNCHANGED x\n" //
				+ "Next == A \\/ B\n" //
				+ "====\n");
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("S")
				+ "\",\"workers\":2,\"deadlock\":false,\"coverage\":false,\"store\":false}");
		final JsonObject paused = h.ok("{\"command\":\"check\",\"budget_states\":3}");
		assertFalse(paused.get("finished").getAsBoolean());

		final Field f = Resident.class.getDeclaredField("checker");
		f.setAccessible(true);
		final ModelChecker checker = (ModelChecker) f.get(h.resident);
		final Method periodicSuspend = ModelChecker.class.getDeclaredMethod("periodicSuspend");
		final Method periodicResume = ModelChecker.class.getDeclaredMethod("periodicResume");
		periodicSuspend.setAccessible(true);
		periodicResume.setAccessible(true);

		final ExecutorService pool = Executors.newFixedThreadPool(2);
		try {
			for (int round = 0; round < 3; round++) {
				checker.resume();
				// Let the workers get into their (slow) expansions.
				Thread.sleep(30);
				final Future<?> periodic = pool.submit(() -> periodicSuspend.invoke(checker));
				final Future<?> pause = pool.submit(() -> {
					checker.suspend();
					return null;
				});
				periodic.get(30, TimeUnit.SECONDS);
				pause.get(30, TimeUnit.SECONDS);
				// The periodic work ends; the resident's pause still holds.
				periodicResume.invoke(checker);
			}
		} finally {
			pool.shutdownNow();
		}

		final JsonObject done = h.ok("{\"command\":\"check\"}");
		assertTrue(done.get("finished").getAsBoolean());
		assertEquals("ok", done.get("verdict").getAsString());
		assertEquals(25, done.getAsJsonObject("stats").get("distinct").getAsLong());
		h.resident.shutdown();
	}
}
