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
package tlc2;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.After;
import org.junit.Test;

public class TLCGlobalsContinuationTraceTest {

	@After
	public void restore() {
		TLCGlobals.continuationTraceLimit = -1;
		TLCGlobals.resetContinuationTraces();
	}

	@Test
	public void unlimitedByDefault() {
		TLCGlobals.continuationTraceLimit = -1;
		for (int i = 0; i < 10; i++) {
			assertTrue(TLCGlobals.continuationTraceAllowed("Inv"));
		}
	}

	@Test
	public void capIsPerProperty() {
		TLCGlobals.continuationTraceLimit = 2;
		assertTrue(TLCGlobals.continuationTraceAllowed("Inv"));
		assertTrue(TLCGlobals.continuationTraceAllowed("Inv"));
		assertFalse(TLCGlobals.continuationTraceAllowed("Inv"));
		assertTrue(TLCGlobals.continuationTraceAllowed("Other"));
		assertTrue(TLCGlobals.continuationTraceAllowed(null));
		TLCGlobals.resetContinuationTraces();
		assertTrue(TLCGlobals.continuationTraceAllowed("Inv"));
	}

	@Test
	public void zeroPrintsNone() {
		TLCGlobals.continuationTraceLimit = 0;
		assertFalse(TLCGlobals.continuationTraceAllowed("Inv"));
	}
}
