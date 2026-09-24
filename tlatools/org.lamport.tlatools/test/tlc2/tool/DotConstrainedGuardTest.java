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
package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.Test;

import tla2sany.semantic.SemanticNode;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.util.DotStateWriter;
import tlc2.util.IStateWriter;
import util.FileUtil;

/**
 * Guards that evaluate false before any primed variable is assigned reach a
 * constrained writer through {@link IStateWriter#writeUnsatisfied}; the
 * default must not hand {@link DotStateWriter} a partially assigned
 * successor (it fingerprints it).
 */
public class DotConstrainedGuardTest extends ModelCheckerTestCase {

	public DotConstrainedGuardTest() {
		super("Guards", "basis",
				new String[] { "-deadlock", "-dump", "dot,constrained",
						"${metadir}" + FileUtil.separator + DotConstrainedGuardTest.class.getCanonicalName() + ".dot" },
				ExitStatus.SUCCESS);
	}

	@Override
	protected boolean doDump() {
		return false;
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	private final AtomicBoolean partial = new AtomicBoolean(false);
	private final AtomicInteger unsatisfied = new AtomicInteger();

	@Override
	protected IStateWriter getStateWriter(final IStateWriter sw) {
		try {
			return new DotStateWriter(sw.getDumpFileName(), "strict ", false, false, false, true, false, false) {
				@Override
				public void writeUnsatisfied(final TLCState state, final Action action, final TLCState successor,
						final SemanticNode pred, final tlc2.util.Context c) {
					unsatisfied.incrementAndGet();
					super.writeUnsatisfied(state, action, successor, pred, c);
				}

				@Override
				public void writeState(final TLCState state, final TLCState successor, final short stateFlags,
						final Action action, final SemanticNode pred) {
					if (!successor.allAssigned()) {
						partial.set(true);
					}
					super.writeState(state, successor, stateFlags, action, pred);
				}
			};
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
		// The false guards were reported (A, B and C are each blocked
		// somewhere) but never forwarded with unassigned variables.
		assertTrue(unsatisfied.get() > 0);
		assertFalse(partial.get());
	}
}
