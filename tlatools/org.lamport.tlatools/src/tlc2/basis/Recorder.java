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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;

import tlc2.module.Json;
import tlc2.output.EC;
import tlc2.output.IMessagePrinterRecorder;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.value.IValue;
import util.UniqueString;

/**
 * Keeps what TLC reports, typed, instead of printing it.
 *
 * TLC's {@link tlc2.output.MP} hands every message to the registered
 * recorder as its error code plus the objects the message was built from,
 * before rendering them to text. Counterexample states arrive as
 * {@link TLCStateInfo} objects, so a trace can be handed on as values rather
 * than re-parsed out of the printed form. Everything else is kept as the
 * code and its parameters' string forms, for the artifact.
 */
public final class Recorder implements IMessagePrinterRecorder {

	/** A counterexample being assembled from TLC_STATE_PRINT2 messages. */
	public static final class Trace {
		/** Why TLC printed a trace: the code that opened it. */
		public int code;
		/** The invariant or property named by that code, when it names one. */
		public String property;
		public final List<JsonObject> states = new ArrayList<>();
		/** True once TLC said the trace ends in stuttering. */
		public boolean stuttering;
		/** The ordinal the lasso loops back to, or null. */
		public Integer lassoTo;
		/**
		 * For a violation in an initial state: the state as TLC printed it
		 * into the report. TLC prints no trace for such a violation, so the
		 * one-state trace is completed from this by {@link Recorder#completeInitial}.
		 */
		public String initialText;
	}

	/** Whether a code reports a violation in an initial state, which TLC prints no trace for. */
	private static boolean isInitialViolation(final int code) {
		return code == EC.TLC_INVARIANT_VIOLATED_INITIAL || code == EC.TLC_PROPERTY_VIOLATED_INITIAL;
	}

	private final List<JsonObject> messages = new ArrayList<>();
	private Trace trace;
	private Trace finishedTrace;
	/** Every counterexample TLC printed, in order (several under continuation). */
	private final List<Trace> traces = new ArrayList<>();
	/** How often each property was reported violated. */
	private final java.util.LinkedHashMap<String, Integer> violationCounts = new java.util.LinkedHashMap<>();
	/** Reports past the per-property trace cap, per property: counted, not kept as messages. */
	private final java.util.LinkedHashMap<String, Long> untraced = new java.util.LinkedHashMap<>();
	/** Invariants whose evaluation failed, to the first failure's message. */
	private final java.util.LinkedHashMap<String, String> evaluationFailures = new java.util.LinkedHashMap<>();
	private JsonObject finalStats;
	private int outcome = EC.NO_ERROR;
	private String outcomeProperty;

	@Override
	public synchronized void record(final int code, final Object... objects) {
		if ((code == EC.TLC_INVARIANT_VIOLATED_BEHAVIOR || code == EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR)
				&& objects != null && objects.length > 0) {
			final String property = String.valueOf(objects[0]);
			if (tlc2.TLCGlobals.continuationTraceCapped(property)) {
				// Past the per-property trace cap under continuation: no trace
				// follows, so the report is counted, not kept. A run whose
				// invariant fails on most states would otherwise keep a
				// message and an empty trace per state.
				if (outcome == EC.NO_ERROR) {
					outcome = code;
					outcomeProperty = property;
				}
				violationCounts.merge(property, 1, Integer::sum);
				untraced.merge(property, 1L, Long::sum);
				trace = null;
				return;
			}
		}
		final JsonObject message = new JsonObject();
		message.addProperty("code", code);
		final JsonArray params = new JsonArray();
		if (objects != null) {
			for (final Object o : objects) {
				if (o instanceof TLCStateInfo) {
					// A stuttering tail (TLC_STATE_PRINT3) comes with a null state.
					final TLCStateInfo info = (TLCStateInfo) o;
					params.add(info.state == null ? JsonParser.parseString("null") : stateInfo(info));
				} else if (o instanceof TLCState) {
					params.add(state((TLCState) o));
				} else if (o instanceof Object[]) {
					final JsonArray inner = new JsonArray();
					for (final Object i : (Object[]) o) {
						inner.add(String.valueOf(i));
					}
					params.add(inner);
				} else {
					params.add(String.valueOf(o));
				}
			}
		}
		message.add("params", params);
		messages.add(message);

		switch (code) {
		case EC.TLC_INVARIANT_VIOLATED_INITIAL:
		case EC.TLC_INVARIANT_VIOLATED_BEHAVIOR:
		case EC.TLC_INVARIANT_VIOLATED_LEVEL:
		case EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR:
		case EC.TLC_TEMPORAL_PROPERTY_VIOLATED:
		case EC.TLC_PROPERTY_VIOLATED_INITIAL:
		case EC.TLC_DEADLOCK_REACHED:
		case EC.TLC_INVARIANT_EVALUATION_FAILED:
			final String property = objects != null && objects.length > 0 && !(objects[0] instanceof TLCState)
					&& !(objects[0] instanceof TLCStateInfo)
					? String.valueOf(objects[0])
					: null;
			if (outcome == EC.NO_ERROR) {
				outcome = code;
				outcomeProperty = property;
			}
			if (code == EC.TLC_INVARIANT_EVALUATION_FAILED) {
				// The invariant did not evaluate: that is no verdict on it, so
				// it is kept apart from the violations.
				evaluationFailures.putIfAbsent(property == null ? "" : property,
						objects != null && objects.length > 1 ? String.valueOf(objects[1]) : "");
			} else {
				violationCounts.merge(property == null ? "" : property, 1, Integer::sum);
			}
			trace = new Trace();
			trace.code = code;
			trace.property = property;
			if (isInitialViolation(code) && objects != null && objects.length > 1) {
				trace.initialText = String.valueOf(objects[1]);
			}
			traces.add(trace);
			break;
		case EC.TLC_BEHAVIOR_UP_TO_THIS_POINT:
			// The behaviour is printed from its first state on. When TLC prints
			// it again for the same report (an evaluation error re-run to
			// rebuild its call stack), the reprint replaces what came before.
			if (trace != null && !trace.states.isEmpty()) {
				trace.states.clear();
				trace.stuttering = false;
				trace.lassoTo = null;
			}
			break;
		case EC.TLC_STATE_PRINT1:
			// A single state (an initial-state violation): no ordinal.
			if (trace == null) {
				trace = new Trace();
				trace.code = code;
			}
			// MP.printState wraps the state in a TLCStateInfo; a bare TLCState
			// is kept too, for any caller that records it directly.
			final JsonObject single = objects == null || objects.length == 0 ? null
					: objects[0] instanceof TLCStateInfo && ((TLCStateInfo) objects[0]).state != null
							? stateInfo((TLCStateInfo) objects[0])
							: objects[0] instanceof TLCState ? state((TLCState) objects[0]) : null;
			if (single != null) {
				single.addProperty("ordinal", trace.states.size() + 1);
				trace.states.add(single);
			}
			finishedTrace = trace;
			break;
		case EC.TLC_STATE_PRINT2:
			if (trace == null) {
				trace = new Trace();
				trace.code = code;
			}
			if (objects != null && objects.length >= 2 && objects[0] instanceof TLCStateInfo
					&& ((TLCStateInfo) objects[0]).state != null) {
				final JsonObject s = stateInfo((TLCStateInfo) objects[0]);
				s.addProperty("ordinal", objects[1] instanceof Integer ? (Integer) objects[1] : trace.states.size() + 1);
				trace.states.add(s);
			}
			finishedTrace = trace;
			break;
		case EC.TLC_STATE_PRINT3:
			if (trace != null) {
				trace.stuttering = true;
				finishedTrace = trace;
			}
			break;
		case EC.TLC_BACK_TO_STATE:
			if (trace != null && objects != null && objects.length >= 1) {
				try {
					trace.lassoTo = objects[0] instanceof TLCStateInfo && objects.length >= 2
							? (Integer) objects[1]
							: Integer.parseInt(String.valueOf(objects[0]));
				} catch (final NumberFormatException e) {
					trace.lassoTo = null;
				}
				finishedTrace = trace;
			}
			break;
		case EC.TLC_STATS:
			if (objects != null && objects.length >= 3) {
				finalStats = new JsonObject();
				finalStats.addProperty("generated", parseLong(objects[0]));
				finalStats.addProperty("distinct", parseLong(objects[1]));
				finalStats.addProperty("queue", parseLong(objects[2]));
			}
			break;
		default:
			break;
		}
	}

	private static Long parseLong(final Object o) {
		try {
			return Long.parseLong(String.valueOf(o).replace(",", ""));
		} catch (final NumberFormatException e) {
			return null;
		}
	}

	/** Forget every counterexample and verdict, for a run that starts over. */
	public synchronized void reset() {
		messages.clear();
		trace = null;
		finishedTrace = null;
		traces.clear();
		violationCounts.clear();
		untraced.clear();
		evaluationFailures.clear();
		finalStats = null;
		outcome = EC.NO_ERROR;
		outcomeProperty = null;
	}

	/** The messages recorded so far, oldest first, and forget them. */
	public synchronized JsonArray drainMessages() {
		final JsonArray out = new JsonArray();
		for (final JsonObject m : messages) {
			out.add(m);
		}
		messages.clear();
		return out;
	}

	/**
	 * Give every violation in an initial state its one-state trace. TLC prints
	 * the state only into the report's text, so {@code resolve} maps that text
	 * to the state as a typed value ({@link #state}), or returns null, and the
	 * state is then kept as TLC printed it, under {@code "tla"}. Such a trace
	 * becomes the last complete counterexample when no other has been printed.
	 */
	public synchronized void completeInitial(final java.util.function.Function<String, JsonObject> resolve) {
		for (final Trace t : traces) {
			if (!isInitialViolation(t.code) || !t.states.isEmpty() || t.initialText == null) {
				continue;
			}
			JsonObject s = resolve == null ? null : resolve.apply(t.initialText);
			if (s == null) {
				s = new JsonObject();
				s.addProperty("tla", t.initialText);
			}
			s.addProperty("action", "<Initial predicate>");
			s.addProperty("ordinal", 1);
			t.states.add(s);
			if (finishedTrace == null) {
				finishedTrace = t;
			}
		}
	}

	/** The last complete counterexample, or null. */
	public synchronized Trace trace() {
		return finishedTrace;
	}

	/** Every counterexample TLC printed so far, oldest first. */
	public synchronized List<Trace> traces() {
		return new ArrayList<>(traces);
	}

	/** Property name to the number of times TLC reported it violated. */
	public synchronized Map<String, Integer> violationCounts() {
		return new java.util.LinkedHashMap<>(violationCounts);
	}

	/** Invariant name to the message of its first failed evaluation. */
	public synchronized Map<String, String> evaluationFailures() {
		return new java.util.LinkedHashMap<>(evaluationFailures);
	}

	/** Property name to the reports past its trace cap, which carry no message or trace. */
	public synchronized JsonObject untracedReports() {
		final JsonObject out = new JsonObject();
		untraced.forEach(out::addProperty);
		return out;
	}

	/** The `TLC_STATS` line TLC prints at the end of a run, or null. */
	public synchronized JsonObject finalStats() {
		return finalStats;
	}

	/** The first violation code, or {@link EC#NO_ERROR}. */
	public synchronized int outcome() {
		return outcome;
	}

	public synchronized String outcomeProperty() {
		return outcomeProperty;
	}

	/** Render a trace state with its action and the value of every variable. */
	public static JsonObject stateInfo(final TLCStateInfo info) {
		final JsonObject s = state(info.state);
		s.addProperty("action", String.valueOf(info.info));
		if (info.fp != null) {
			s.addProperty("fp", info.fp);
		}
		return s;
	}

	/**
	 * A state as `{"fp": ..., "vars": {name: value}}`. Values go through the
	 * Json module's encoder (records, tuples and sequences become objects and
	 * arrays); a value it cannot encode keeps its TLA+ printed form under
	 * `"tla"`.
	 */
	public static JsonObject state(final TLCState state) {
		final JsonObject s = new JsonObject();
		try {
			s.addProperty("fp", state.fingerPrint());
		} catch (final RuntimeException e) {
			// A state with unassigned variables has no fingerprint.
		}
		final JsonObject vars = new JsonObject();
		final Map<UniqueString, IValue> vals = state.getVals();
		if (vals != null) {
			for (final Map.Entry<UniqueString, IValue> e : vals.entrySet()) {
				vars.add(e.getKey().toString(), value(e.getValue()));
			}
		}
		s.add("vars", vars);
		return s;
	}

	public static JsonElement value(final IValue value) {
		if (value == null) {
			return JsonParser.parseString("null");
		}
		try {
			return JsonParser.parseString(Json.toJson(value).val.toString());
		} catch (final Exception e) {
			final JsonObject o = new JsonObject();
			o.add("tla", new JsonPrimitive(value.toString()));
			return o;
		}
	}
}
