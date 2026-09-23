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
 * A successor a state constraint excludes is tallied as a constraint row, not
 * as a guard of the action that generated it, and is counted apart from the
 * false guards.
 */
public class GraphStoreConstraintTest extends ModelCheckerTestCase {

	public GraphStoreConstraintTest() {
		super("GuardsConstraint", "basis", new String[] { "-deadlock" }, ExitStatus.SUCCESS);
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

		// 0 -A-> 1 -A-> 2; A's step from 2 to 3 is excluded by Small.
		assertEquals(3, store.states());
		assertEquals(2, store.edges());

		final Map<String, GraphStore.Blocked> rows = new HashMap<>();
		for (final GraphStore.Blocked b : store.blocked()) {
			rows.put(b.kind + " " + b.action, b);
		}
		assertEquals(rows.toString(), 2, rows.size());
		// B's guard fails at 0, 1 and 2.
		final GraphStore.Blocked guard = rows.get("guard B");
		assertNotNull(rows.keySet().toString(), guard);
		assertEquals("x=10", guard.text);
		assertEquals(3, guard.count);
		// The constraint dropped one successor A generated.
		final GraphStore.Blocked constraint = rows.get("constraint A");
		assertNotNull(rows.keySet().toString(), constraint);
		assertEquals(1, constraint.count);
		assertEquals(3, store.unsatisfied());
		assertEquals(1, store.excluded());
	}
}
