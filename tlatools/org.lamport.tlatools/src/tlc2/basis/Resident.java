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

import java.io.BufferedReader;
import java.io.File;
import java.io.FileDescriptor;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;
import tlc2.tool.ModelChecker;
import tlc2.tool.TLCState;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.FPSetFactory;
import tlc2.util.FP64;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.util.NoopStateWriter;
import util.FileUtil;
import util.SimpleFilenameToStream;
import util.ToolIO;

/**
 * TLC as a resident service: one JVM, one parsed spec, one state graph, kept
 * alive between requests and driven over JSON lines.
 *
 * <p>
 * Each request is one JSON object on a line of standard input; each reply is
 * one JSON object on a line of standard output. Everything TLC would print
 * goes to standard error instead, so the protocol owns stdout. Requests:
 *
 * <ul>
 * <li>{@code open}: parse {@code spec} (a .tla path) with {@code config} (a
 * .cfg path, default the spec's), build the checker, and answer with the
 * catalogue: actions, invariants, implied actions, temporal properties and
 * variables. Nothing is explored yet. {@code workers} sets the thread count,
 * {@code metadir} where TLC keeps its state files, {@code deadlock} (default
 * true) whether deadlocks are violations.</li>
 * <li>{@code check}: explore, resuming where the last check stopped, until
 * the reachable graph is exhausted, a violation is found, or the budget runs
 * out: {@code budget_ms} of wall time, {@code budget_states} distinct
 * states. The reply carries {@code finished}, the {@code verdict}, the
 * counterexample {@code trace} when there is one, the statistics, and the
 * typed messages TLC produced during the call.</li>
 * <li>{@code stats}: the counters, without exploring.</li>
 * <li>{@code close}: stop, and exit the process.</li>
 * </ul>
 *
 * <p>
 * TLC is built around static state ({@link TLCGlobals}, {@link MP}), so one
 * process serves one spec: a second {@code open} is refused.
 */
public final class Resident {

	private final Recorder recorder = new Recorder();
	private Tool tool;
	private ModelChecker checker;
	private Thread checkerThread;
	private String metadir;
	private volatile Integer resultCode;
	private volatile Throwable checkerFailure;
	private long openedAt;
	private long exploringMs;

	public static void main(final String[] args) throws IOException {
		// The protocol owns stdout; TLC's own printing goes to stderr.
		final PrintStream protocol = new PrintStream(new FileOutputStream(FileDescriptor.out), true,
				StandardCharsets.UTF_8.name());
		final PrintStream sink = new PrintStream(new FileOutputStream(FileDescriptor.err), true,
				StandardCharsets.UTF_8.name());
		System.setOut(sink);
		ToolIO.out = sink;
		ToolIO.err = sink;
		ToolIO.setMode(ToolIO.TOOL);

		final Resident resident = new Resident();
		MP.setRecorder(resident.recorder);

		final JsonObject ready = new JsonObject();
		ready.addProperty("event", "ready");
		ready.addProperty("tlc_version", TLCGlobals.Version.number());
		ready.addProperty("tlc_revision", TLCGlobals.Version.revisionOrDev());
		protocol.println(ready);

		final BufferedReader in = new BufferedReader(
				new InputStreamReader(System.in, StandardCharsets.UTF_8));
		String line;
		while ((line = in.readLine()) != null) {
			if (line.isBlank()) {
				continue;
			}
			JsonObject request;
			try {
				request = JsonParser.parseString(line).getAsJsonObject();
			} catch (final RuntimeException e) {
				protocol.println(error(null, "invalid_request", "not a JSON object: " + e.getMessage()));
				continue;
			}
			final JsonElement id = request.get("id");
			final String command = string(request, "command", "");
			JsonObject reply;
			try {
				reply = resident.dispatch(command, request);
			} catch (final Throwable t) {
				reply = error(id, "internal", t.toString());
				reply.add("messages", resident.recorder.drainMessages());
			}
			if (id != null) {
				reply.add("id", id);
			}
			reply.addProperty("command", command);
			protocol.println(reply);
			if ("close".equals(command)) {
				break;
			}
		}
		resident.shutdown();
		System.exit(0);
	}

	private JsonObject dispatch(final String command, final JsonObject request) throws Exception {
		switch (command) {
		case "open":
			return open(request);
		case "check":
			return check(request);
		case "stats": {
			final JsonObject reply = ok();
			reply.add("stats", stats());
			return reply;
		}
		case "close":
			return ok();
		default:
			return error(null, "unknown_command", "no such request: " + command);
		}
	}

	// ─── open ───────────────────────────────────────────────────────────

	private JsonObject open(final JsonObject request) {
		if (tool != null) {
			return error(null, "already_open", "this process already serves " + tool.getRootFile()
					+ "; close it and start another");
		}
		final String spec = string(request, "spec", null);
		if (spec == null) {
			return error(null, "invalid_request", "open needs `spec`, the path of a .tla file");
		}
		final File specFile = new File(spec).getAbsoluteFile();
		if (!specFile.isFile()) {
			return error(null, "no_such_file", "no spec at " + specFile);
		}
		final String specDir = specFile.getParent() + FileUtil.separator;
		final String mainFile = specFile.getName().replaceFirst("\\.tla$", "");
		String config = string(request, "config", null);
		if (config == null) {
			config = mainFile;
		} else {
			final File c = new File(config).getAbsoluteFile();
			config = c.getName().replaceFirst("\\.cfg$", "");
			if (!c.getParentFile().equals(specFile.getParentFile())) {
				return error(null, "invalid_request",
						"config must live next to the spec (TLC resolves it in the spec's directory)");
			}
		}
		final int workers = request.has("workers") ? request.get("workers").getAsInt()
				: Runtime.getRuntime().availableProcessors();
		final boolean deadlock = !request.has("deadlock") || request.get("deadlock").getAsBoolean();
		final boolean coverage = !request.has("coverage") || request.get("coverage").getAsBoolean();
		final int fpIndex = request.has("fp_index") ? request.get("fp_index").getAsInt() : 0;
		if (request.has("metadir")) {
			TLCGlobals.metaDir = new File(request.get("metadir").getAsString()).getAbsolutePath()
					+ FileUtil.separator;
		}

		openedAt = System.currentTimeMillis();
		recorder.drainMessages();
		try {
			TLCGlobals.setNumWorkers(workers);
			// Coverage is read into `static final` fields when ModelChecker and
			// Worker load, so it is decided here, before either class is used.
			// The interval only paces TLC's own printing, which goes to stderr.
			TLCGlobals.coverageInterval = coverage ? Integer.MAX_VALUE : -1;
			FP64.Init(fpIndex);
			metadir = FileUtil.makeMetaDir(new Date(openedAt), specDir, null);
			tool = new FastTool(mainFile, config, new SimpleFilenameToStream(specDir), Tool.Mode.MC,
					new HashMap<>());
			final boolean checkDeadlock = deadlock && tool.getModelConfig().getCheckDeadlock();
			checker = new ModelChecker(tool, metadir, new NoopStateWriter(), checkDeadlock, null,
					FPSetFactory.getFPSetInitialized(new FPSetConfiguration(), metadir, specFile.getName()),
					openedAt);
			TLCGlobals.mainChecker = checker;
		} catch (final Throwable t) {
			tool = null;
			checker = null;
			final JsonObject reply = error(null, "open_failed", t.toString());
			reply.add("messages", recorder.drainMessages());
			return reply;
		}

		final JsonObject reply = ok();
		reply.addProperty("spec", specFile.getPath());
		reply.addProperty("root_module", tool.getRootName());
		reply.addProperty("metadir", metadir);
		reply.addProperty("workers", workers);
		reply.addProperty("check_deadlock", deadlock && tool.getModelConfig().getCheckDeadlock());
		reply.addProperty("coverage", coverage);
		reply.addProperty("fp_index", fpIndex);
		reply.add("catalogue", catalogue());
		reply.add("messages", recorder.drainMessages());
		return reply;
	}

	private JsonObject catalogue() {
		final JsonObject c = new JsonObject();
		final JsonArray actions = new JsonArray();
		for (final Action a : tool.getActions()) {
			final JsonObject o = new JsonObject();
			o.addProperty("id", a.getId());
			o.addProperty("name", a.getNameOfDefault());
			o.addProperty("location", a.getLocation());
			o.addProperty("internal", a.isInternal());
			actions.add(o);
		}
		c.add("actions", actions);
		c.add("invariants", names(tool.getInvNames()));
		c.add("implied_actions", names(tool.getImpliedActNames()));
		final JsonArray temporals = new JsonArray();
		for (final Action a : tool.getTemporals()) {
			temporals.add(a.getNameOfDefault());
		}
		c.add("temporal_properties", temporals);
		final JsonArray implied = new JsonArray();
		for (final Action a : tool.getImpliedTemporals()) {
			implied.add(a.getNameOfDefault());
		}
		c.add("implied_temporals", implied);
		final JsonArray vars = new JsonArray();
		if (TLCState.Empty != null) {
			for (final String v : TLCState.Empty.getVarsAsStrings()) {
				vars.add(v);
			}
		}
		c.add("variables", vars);
		c.addProperty("state_constraints", tool.getModelConstraints().length);
		c.addProperty("action_constraints", tool.getActionConstraints().length);
		c.addProperty("symmetry", tool.getSymmetryPerms() != null);
		return c;
	}

	private static JsonArray names(final String[] names) {
		final JsonArray out = new JsonArray();
		if (names != null) {
			for (final String n : names) {
				out.add(n);
			}
		}
		return out;
	}

	// ─── check ──────────────────────────────────────────────────────────

	private JsonObject check(final JsonObject request) throws InterruptedException {
		if (checker == null) {
			return error(null, "not_open", "open a spec first");
		}
		final long budgetMs = request.has("budget_ms") ? request.get("budget_ms").getAsLong() : Long.MAX_VALUE;
		final long budgetStates = request.has("budget_states") ? request.get("budget_states").getAsLong()
				: Long.MAX_VALUE;
		final long distinctAtStart = checker.getDistinctStatesGenerated();
		final long started = System.currentTimeMillis();
		if (request.has("continue")) {
			// Keep exploring past a violation, so one run reports every
			// invariant's verdict. Process-global, as TLC's -continue is.
			TLCGlobals.continuation = request.get("continue").getAsBoolean();
		}

		if (resultCode == null && checkerFailure == null) {
			if (checkerThread == null) {
				checkerThread = new Thread(() -> {
					try {
						resultCode = checker.modelCheck();
					} catch (final Throwable t) {
						checkerFailure = t;
					}
				}, "tlc-resident-checker");
				checkerThread.setDaemon(true);
				checkerThread.start();
			} else {
				checker.resume();
			}
			// Wait for the run to end or the budget to run out. The queue's
			// suspend blocks until every worker has parked, so on return the
			// counters are quiescent.
			boolean suspended = false;
			while (checkerThread.isAlive()) {
				final long now = System.currentTimeMillis();
				final boolean overTime = now - started >= budgetMs;
				final boolean overStates = checker.getDistinctStatesGenerated() - distinctAtStart >= budgetStates;
				if (overTime || overStates) {
					checker.suspend();
					suspended = true;
					break;
				}
				checkerThread.join(20);
			}
			exploringMs += System.currentTimeMillis() - started;
			if (!suspended) {
				checkerThread.join();
			}
		}

		final JsonObject reply = ok();
		final boolean finished = !checkerThread.isAlive();
		reply.addProperty("finished", finished);
		reply.addProperty("budget_exhausted", !finished);
		if (checkerFailure != null) {
			reply.addProperty("verdict", "error");
			reply.addProperty("error", checkerFailure.toString());
		} else if (finished) {
			reply.addProperty("result_code", resultCode);
			reply.addProperty("verdict", verdict(resultCode, recorder.outcome()));
		} else {
			reply.addProperty("verdict", "unfinished");
		}
		final String property = recorder.outcomeProperty();
		if (property != null) {
			reply.addProperty("violated", property);
		}
		final Recorder.Trace trace = recorder.trace();
		if (trace != null) {
			reply.add("trace", traceJson(trace));
		}
		final JsonArray all = new JsonArray();
		for (final Recorder.Trace t : recorder.traces()) {
			all.add(traceJson(t));
		}
		reply.add("traces", all);
		reply.add("invariants", invariantVerdicts(finished));
		reply.addProperty("continuation", TLCGlobals.continuation);
		reply.add("stats", stats());
		reply.add("messages", recorder.drainMessages());
		return reply;
	}

	private static JsonObject traceJson(final Recorder.Trace trace) {
		final JsonObject t = new JsonObject();
		t.addProperty("code", trace.code);
		t.addProperty("property", trace.property);
		t.addProperty("length", trace.states.size());
		t.addProperty("stuttering", trace.stuttering);
		if (trace.lassoTo != null) {
			t.addProperty("lasso_to", trace.lassoTo);
		}
		final JsonArray states = new JsonArray();
		for (final JsonObject s : trace.states) {
			states.add(s);
		}
		t.add("states", states);
		return t;
	}

	/**
	 * One verdict per configured invariant. A violated one carries the level
	 * and last action of the first counterexample TLC printed for it, and how
	 * many times it was reported (more than one only under continuation). One
	 * that was never reported is `no_violation_found` when the run finished
	 * without error and `not_evaluated` otherwise: a run that stopped at the
	 * first violation, or at its budget, evaluated it on some states only.
	 */
	private JsonArray invariantVerdicts(final boolean finished) {
		final JsonArray out = new JsonArray();
		final Map<String, Integer> counts = recorder.violationCounts();
		final List<Recorder.Trace> traces = recorder.traces();
		final boolean exhausted = finished && checkerFailure == null && resultCode != null
				&& (resultCode == EC.NO_ERROR || TLCGlobals.continuation);
		for (final String name : tool.getInvNames()) {
			final JsonObject v = new JsonObject();
			v.addProperty("name", name);
			final Integer n = counts.get(name);
			if (n != null) {
				v.addProperty("verdict", "violated");
				v.addProperty("reports", n);
				for (final Recorder.Trace t : traces) {
					if (name.equals(t.property)) {
						v.addProperty("level", t.states.size());
						if (!t.states.isEmpty()) {
							v.add("action", t.states.get(t.states.size() - 1).get("action"));
						}
						break;
					}
				}
			} else {
				v.addProperty("verdict", exhausted ? "no_violation_found" : "not_evaluated");
			}
			out.add(v);
		}
		return out;
	}

	private static String verdict(final int code, final int outcome) {
		switch (outcome) {
		case EC.TLC_INVARIANT_VIOLATED_INITIAL:
		case EC.TLC_INVARIANT_VIOLATED_BEHAVIOR:
		case EC.TLC_INVARIANT_VIOLATED_LEVEL:
			return "invariant_violated";
		case EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR:
			return "action_property_violated";
		case EC.TLC_TEMPORAL_PROPERTY_VIOLATED:
			return "temporal_property_violated";
		case EC.TLC_DEADLOCK_REACHED:
			return "deadlock";
		case EC.TLC_INVARIANT_EVALUATION_FAILED:
			return "evaluation_failed";
		default:
			return code == EC.NO_ERROR ? "ok" : "error";
		}
	}

	// ─── stats ──────────────────────────────────────────────────────────

	private JsonObject stats() {
		final JsonObject s = new JsonObject();
		if (checker == null) {
			return s;
		}
		final JsonObject fin = recorder.finalStats();
		if (fin != null && resultCode != null) {
			// After the run the fingerprint set is closed; the counts TLC
			// printed at the end are the ones on record.
			s.add("generated", fin.get("generated"));
			s.add("distinct", fin.get("distinct"));
			s.add("queue", fin.get("queue"));
		} else {
			s.addProperty("generated", checker.getStatesGenerated());
			s.addProperty("distinct", checker.getDistinctStatesGenerated());
			s.addProperty("queue", checker.getStateQueueSize());
		}
		s.addProperty("initial", checker.getInitialStatesGenerated());
		s.addProperty("diameter", checker.getProgress());
		s.addProperty("exploring_ms", exploringMs);
		s.addProperty("since_open_ms", System.currentTimeMillis() - openedAt);
		s.addProperty("running", checkerThread != null && checkerThread.isAlive());
		s.addProperty("finished", resultCode != null);
		return s;
	}

	private void shutdown() {
		if (checker != null && checkerThread != null && checkerThread.isAlive()) {
			checker.stop();
			try {
				checkerThread.join(5000);
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		}
	}

	// ─── replies ────────────────────────────────────────────────────────

	private static JsonObject ok() {
		final JsonObject o = new JsonObject();
		o.addProperty("ok", true);
		return o;
	}

	private static JsonObject error(final JsonElement id, final String code, final String message) {
		final JsonObject o = new JsonObject();
		o.addProperty("ok", false);
		o.addProperty("error_code", code);
		o.addProperty("error", message);
		if (id != null) {
			o.add("id", id);
		}
		return o;
	}

	private static String string(final JsonObject o, final String key, final String dflt) {
		return o.has(key) && !o.get(key).isJsonNull() ? o.get(key).getAsString() : dflt;
	}
}
