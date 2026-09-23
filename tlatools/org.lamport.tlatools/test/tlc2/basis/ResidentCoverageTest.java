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

import java.util.HashMap;
import java.util.Map;

import org.junit.Test;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * Coverage as data: a conjunct no evaluation reached is listed under
 * {@code unevaluated}, a primed conjunct (an assignment) is not, and an
 * action whose guards all ran lists nothing. After an incremental refresh
 * the coverage is still the run's, marked stale, not an empty tree.
 */
public class ResidentCoverageTest {

	private static String spec(final int dLimit) {
		return "---- MODULE V ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES x\n" //
				+ "Init == x = 0\n" //
				+ "A == x < 3 /\\ x' = x + 1\n" //
				+ "D == x > " + dLimit + " /\\ x * 2 > 25 /\\ x' = 0\n" //
				+ "Next == A \\/ D\n" //
				+ "====\n";
	}

	@Test
	public void testUnevaluated() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("V.cfg", "INIT Init\nNEXT Next\n");
		h.write("V.tla", spec(10));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("V") + "\",\"workers\":1,\"deadlock\":false}");
		h.ok("{\"command\":\"check\"}");
		final JsonObject coverage = h.ok("{\"command\":\"coverage\"}").getAsJsonObject("coverage");
		assertTrue(coverage.get("enabled").getAsBoolean());
		final Map<String, JsonObject> actions = new HashMap<>();
		for (final JsonElement e : coverage.getAsJsonArray("actions")) {
			actions.put(e.getAsJsonObject().get("name").getAsString(), e.getAsJsonObject());
		}
		assertEquals(3, actions.get("A").get("found").getAsLong());
		assertEquals(0, actions.get("A").getAsJsonArray("unevaluated").size());
		assertEquals(0, actions.get("D").get("found").getAsLong());
		// Past D's first guard nothing ran: the second guard, and the
		// assignment, whose only evaluated part would be its primed side.
		final JsonArray dead = actions.get("D").getAsJsonArray("unevaluated");
		assertEquals(dead.toString(), 2, dead.size());
		assertEquals("x*2>25", dead.get(0).getAsJsonObject().get("text").getAsString());
		assertEquals("x'=0", dead.get(1).getAsJsonObject().get("text").getAsString());
		assertTrue(h.ok("{\"command\":\"coverage\"}").get("stale") == null);

		// Queries over the store evaluate outside the run and leave its
		// coverage as it was.
		final String fp = h.ok("{\"command\":\"screen\",\"candidates\":[\"x # 1\"]}").getAsJsonArray("results")
				.get(0).getAsJsonObject().get("first_violation_fp").getAsString();
		for (int i = 0; i < 3; i++) {
			h.ok("{\"command\":\"neighbours\",\"fp\":\"" + fp + "\"}");
			h.ok("{\"command\":\"eval\",\"fp\":\"" + fp + "\",\"expr\":\"x + 1\"}");
		}
		assertEquals(coverage.toString(), h.ok("{\"command\":\"coverage\"}").getAsJsonObject("coverage").toString());

		// A refresh replaces the tool with one no checker ran; coverage stays
		// the run's, and says it is stale.
		h.write("V.tla", spec(11));
		assertEquals("incremental", h.ok("{\"command\":\"refresh\"}").get("mode").getAsString());
		final JsonObject after = h.ok("{\"command\":\"coverage\"}");
		assertTrue(after.toString(), after.get("stale").getAsBoolean());
		assertEquals(after.toString(), 2, after.getAsJsonObject("coverage").getAsJsonArray("actions").size());
		h.resident.shutdown();
	}
}
