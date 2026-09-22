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
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.Map;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.util.IStateWriter;

/**
 * The store on a real run: every reached state, every edge, and a tally for
 * every guard that evaluated false, including equality and membership guards
 * on unprimed variables, which TLC evaluates before any primed variable is
 * assigned.
 */
public class GraphStoreGuardTest extends ModelCheckerTestCase {

	public GraphStoreGuardTest() {
		super("Guards", "basis", new String[] { "-deadlock" }, ExitStatus.SUCCESS);
	}

	private GraphStore store;

	@Override
	protected boolean doDump() {
		return false;
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Override
	protected int getNumberOfThreads() {
		return 1;
	}

	@Override
	protected IStateWriter getStateWriter(final IStateWriter sw) {
		try {
			store = new GraphStore(Files.createTempDirectory("graphstore").toString());
			return store;
		} catch (IOException e) {
			fail(e.getMessage());
			return null;
		}
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "5", "4", "0"));

		// (0,a) -A-> (1,b) -B-> (2,c); (0,a) -C-> (0,c) -C-> (0,c).
		assertEquals(4, store.states());
		assertEquals(1, store.initialStates());
		assertEquals(4, store.edges());

		final Map<String, Long> counts = new HashMap<>();
		for (final GraphStore.Blocked b : store.blocked()) {
			counts.put(b.action + ": " + b.text, b.count);
		}
		// A's guard fails at (1,b), (0,c), (2,c); B's at (0,a), (0,c), (2,c);
		// C's at (1,b), (2,c).
		assertEquals(Long.valueOf(3), counts.get("A: pc=\"a\""));
		assertEquals(Long.valueOf(3), counts.get("B: pc=\"b\""));
		assertEquals(Long.valueOf(2), counts.get("C: x<1"));
		assertEquals(3, counts.size());
		assertEquals(8, store.unsatisfied());

		// Every stored state reads back, and the deepest one's path is the
		// three-state behaviour through A and B.
		long deepest = 0;
		for (final long fp : store.fingerprints()) {
			assertNotNull(store.read(fp));
			if (store.level(fp) == 3) {
				deepest = fp;
			}
		}
		final long[][] path = store.pathTo(deepest);
		assertEquals(3, path.length);
		assertEquals("A", store.action((int) path[1][1]).getNameOfDefault());
		assertEquals("B", store.action((int) path[2][1]).getNameOfDefault());
	}
}
