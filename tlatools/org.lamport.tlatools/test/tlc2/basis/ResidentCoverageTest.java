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

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * Coverage as data: a conjunct no evaluation reached is listed under
 * {@code unevaluated}, a primed conjunct (an assignment) is not, and an
 * action whose guards all ran lists nothing.
 */
public class ResidentCoverageTest {

	@Test
	public void testUnevaluated() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("V.cfg", "INIT Init\nNEXT Next\n");
		h.write("V.tla", "---- MODULE V ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLES x\n" //
				+ "Init == x = 0\n" //
				+ "A == x < 3 /\\ x' = x + 1\n" //
				+ "D == x > 10 /\\ x * 2 > 25 /\\ x' = 0\n" //
				+ "Next == A \\/ D\n" //
				+ "====\n");
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
		assertEquals(1, actions.get("D").getAsJsonArray("unevaluated").size());
		assertEquals("x*2>25", actions.get("D").getAsJsonArray("unevaluated").get(0).getAsJsonObject()
				.get("text").getAsString());
		h.resident.shutdown();
	}
}
