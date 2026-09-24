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

import java.nio.file.Files;
import java.util.stream.Stream;

import org.junit.Test;

import com.google.gson.JsonObject;

/**
 * A refresh keeps its store in a metadir of its own under the spec's
 * directory (TLC removes the run's metadir itself when the run ends): a
 * session that ends removes it.
 */
public class ResidentShutdownCleanupTest {

	private static String spec(final int lim) {
		return "---- MODULE C ----\n" //
				+ "EXTENDS Naturals\n" //
				+ "VARIABLE x\n" //
				+ "Init == x = 0\n" //
				+ "Inc == x < " + lim + " /\\ x' = x + 1\n" //
				+ "Next == Inc\n" //
				+ "====\n";
	}

	private static long storeFiles(final ResidentHarness h) throws Exception {
		try (Stream<java.nio.file.Path> files = Files.walk(h.dir)) {
			return files.filter(p -> p.getFileName().toString().equals("basis.states")).count();
		}
	}

	/** The metadirs left under the spec's directory. */
	private static long metadirs(final ResidentHarness h) throws Exception {
		final java.nio.file.Path states = h.dir.resolve("states");
		if (!Files.isDirectory(states)) {
			return 0;
		}
		try (Stream<java.nio.file.Path> dirs = Files.list(states)) {
			return dirs.count();
		}
	}

	@Test
	public void testShutdownRemovesStoreFiles() throws Exception {
		final ResidentHarness h = new ResidentHarness();
		h.write("C.cfg", "INIT Init\nNEXT Next\n");
		h.write("C.tla", spec(3));
		h.ok("{\"command\":\"open\",\"spec\":\"" + h.spec("C") + "\",\"workers\":1,\"deadlock\":false}");
		assertEquals("ok", h.ok("{\"command\":\"check\"}").get("verdict").getAsString());
		// A refresh stopped by its budget (here, at once) keeps the complete
		// run's store as the base and serves its own, in its own metadir.
		h.write("C.tla", spec(6));
		final JsonObject partial = h.ok("{\"command\":\"refresh\",\"budget_ms\":-1}");
		assertTrue(partial.toString(), partial.get("adopted").getAsBoolean());
		assertFalse(partial.toString(), partial.get("complete").getAsBoolean());
		assertTrue(storeFiles(h) >= 1);
		assertTrue(metadirs(h) >= 1);

		h.resident.shutdown();
		assertEquals(0, storeFiles(h));
		assertEquals(0, metadirs(h));
	}
}
