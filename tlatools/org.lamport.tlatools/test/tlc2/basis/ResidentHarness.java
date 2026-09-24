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

import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

/**
 * Drives a {@link Resident} in-process, one request object at a time, over a
 * spec written into a fresh directory. TLC's statics allow one resident per
 * JVM; the build forks one per test class.
 */
final class ResidentHarness {

	final Path dir;
	final Resident resident = Resident.install();

	ResidentHarness() throws IOException {
		dir = Files.createTempDirectory("resident");
	}

	void write(final String name, final String text) throws IOException {
		Files.write(dir.resolve(name), text.getBytes(StandardCharsets.UTF_8));
	}

	/**
	 * The module's path, escaped for a JSON string literal: tests splice it
	 * into request text, and a Windows path's backslashes are escapes there.
	 */
	String spec(final String module) {
		return dir.resolve(module + ".tla").toString().replace("\\", "\\\\");
	}

	/** Serve {@code json}; the reply must be ok. */
	JsonObject ok(final String json) throws Exception {
		final JsonObject reply = call(json);
		assertTrue(reply.toString(), reply.get("ok").getAsBoolean());
		return reply;
	}

	JsonObject call(final String json) throws Exception {
		return resident.serve(JsonParser.parseString(json).getAsJsonObject());
	}

	static long storeStates(final JsonObject reply) {
		return reply.getAsJsonObject("store").get("states").getAsLong();
	}

	static long storeEdges(final JsonObject reply) {
		return reply.getAsJsonObject("store").get("edges").getAsLong();
	}
}
