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
import tlc2.tool.EvalControl;
import tlc2.tool.StateVec;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tla2sany.semantic.OpDefNode;
import tlc2.debug.TLCDebuggerExpression;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
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
 * true) whether deadlocks are violations, {@code store} (default true)
 * whether to keep the {@link GraphStore} the store queries and refresh
 * need (it costs heap per state and edge, and time: every edge is
 * recorded under one lock).</li>
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
	/**
	 * The tool the checker (or simulator) ran: its cost model holds the
	 * coverage counters. A refresh replaces {@link #tool} with one no checker
	 * ran, so coverage is read from this one.
	 */
	private Tool runTool;
	private GraphStore store;
	private ModelChecker checker;
	/** True after an incremental refresh: the store is current, the checker is not. */
	private boolean refreshed;
	/** Whether the last adopted refresh explored its whole graph; meaningful once {@link #refreshed}. */
	private boolean refreshComplete;
	/**
	 * The last fully explored graph and the tool it was explored under: what
	 * the next refresh replays from. Set by the first refresh from a finished
	 * run and advanced only by a refresh that explored its whole graph, so a
	 * refresh cut short (by its budget or a first violation) leaves the next
	 * one something sound to copy edges from.
	 */
	private Tool baseTool;
	private GraphStore baseStore;
	/** False when opened with {@code store: false}: no store, no store queries. */
	private boolean storing = true;
	/**
	 * Set when a refresh that did not replace the tool left TLC's static
	 * tables unfit for the old spec: why a restart is needed. Every request
	 * that evaluates against the spec is refused from then on.
	 */
	private String restartRequired;
	/** The model config's text when the store was built, to detect edits. */
	private String configText;
	private String specDir;
	private String mainFile;
	private String configName;
	private int workers;
	private boolean checkDeadlock;
	/** Set when opened in simulate mode: random behaviours instead of a graph. */
	private tlc2.tool.Simulator simulator;
	private Thread simulatorThread;
	private volatile Integer simulatorResult;
	private volatile Throwable simulatorFailure;
	/** A budget stop ends the simulator for good; later calls report it. */
	private boolean simulationStoppedByBudget;
	private long simulationMs;
	private Thread checkerThread;
	/**
	 * Whether the run explored past violations when it last explored: what
	 * decides if a run that ended on a violation still covered the graph.
	 * {@link TLCGlobals#continuation} is not it, since a later request may
	 * set that after the run ended.
	 */
	private boolean runContinuation;
	/**
	 * Whether any part of the run explored past violations. Once it has, TLC
	 * checked no further invariant on the states that violated one, so an
	 * invariant it never reported may still fail there, even if a later call
	 * resumed the run without continuation.
	 */
	private boolean everContinued;
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

		final Resident resident = install();

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

	/** A resident whose recorder receives TLC's messages; TLC's statics allow one per process. */
	static Resident install() {
		final Resident resident = new Resident();
		MP.setRecorder(resident.recorder);
		return resident;
	}

	/** Serve one request, as a line of standard input would be served (the tests' entry). */
	JsonObject serve(final JsonObject request) throws Exception {
		return dispatch(string(request, "command", ""), request);
	}

	private JsonObject dispatch(final String command, final JsonObject request) throws Exception {
		switch (command) {
		case "check":
		case "trace":
		case "neighbours":
		case "eval":
		case "screen":
		case "refresh": {
			final JsonObject refusal = restartRefusal();
			if (refusal != null) {
				return refusal;
			}
			break;
		}
		default:
			break;
		}
		switch (command) {
		case "open":
			return open(request);
		case "check":
			return check(request);
		case "stats": {
			final JsonObject reply = ok();
			reply.add("stats", stats());
			markStale(reply);
			return reply;
		}
		case "trace":
			return trace(request);
		case "neighbours":
			return neighbours(request);
		case "eval":
			return eval(request);
		case "screen":
			return screen(request);
		case "guard_profile":
			return guardProfile();
		case "refresh":
			return refresh(request);
		case "simulate":
			return simulate(request);
		case "coverage": {
			if (runTool == null) {
				return notOpen();
			}
			final JsonObject reply = ok();
			reply.add("coverage", tlc2.tool.coverage.CoverageWalk.walk(runTool));
			if (refreshed) {
				reply.addProperty("stale", true);
				reply.addProperty("stale_reason",
						"the store was refreshed incrementally; coverage is the last full run's, over the spec as it was then");
			}
			return reply;
		}
		case "registers": {
			if (checker == null) {
				return notOpen();
			}
			final JsonObject reply = ok();
			reply.add("stats", stats());
			reply.add("registers", registers());
			markStale(reply);
			return reply;
		}
		case "store": {
			final JsonObject reply = ok();
			reply.add("store", storeInfo());
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
		storing = !request.has("store") || request.get("store").getAsBoolean();
		if (request.has("metadir")) {
			TLCGlobals.metaDir = new File(request.get("metadir").getAsString()).getAbsolutePath()
					+ FileUtil.separator;
		}

		final String mode = string(request, "mode", "check");
		if (mode.equals("simulate")) {
			return openSimulate(request, specFile, specDir, mainFile, config, workers, deadlock);
		}
		openedAt = System.currentTimeMillis();
		recorder.drainMessages();
		this.specDir = specDir;
		this.mainFile = mainFile;
		this.configName = config;
		this.workers = workers;
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
			runTool = tool;
			final boolean checkDeadlock = deadlock && tool.getModelConfig().getCheckDeadlock();
			this.checkDeadlock = checkDeadlock;
			configText = readConfig();
			store = storing ? new GraphStore(metadir) : null;
			checker = new ModelChecker(tool, metadir,
					storing ? store : new tlc2.util.NoopStateWriter(), checkDeadlock, null,
					FPSetFactory.getFPSetInitialized(new FPSetConfiguration(), metadir, specFile.getName()),
					openedAt);
			TLCGlobals.mainChecker = checker;
		} catch (final Throwable t) {
			tool = null;
			runTool = null;
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
		reply.addProperty("store", storing);
		reply.add("catalogue", catalogue());
		reply.add("messages", recorder.drainMessages());
		return reply;
	}

	/**
	 * Open for random simulation: a Tool in simulation mode and a
	 * {@link tlc2.tool.Simulator} with {@code depth} (default 100 steps per
	 * behaviour), {@code traces} (default unbounded: run until stopped or a
	 * violation) and {@code seed} (default random, reported).
	 */
	private JsonObject openSimulate(final JsonObject request, final File specFile, final String specDir,
			final String mainFile, final String config, final int workers, final boolean deadlock) {
		openedAt = System.currentTimeMillis();
		recorder.drainMessages();
		this.specDir = specDir;
		this.mainFile = mainFile;
		this.configName = config;
		this.workers = workers;
		final int depth = request.has("depth") ? request.get("depth").getAsInt() : 100;
		final long traces = request.has("traces") ? request.get("traces").getAsLong() : Long.MAX_VALUE;
		final tlc2.util.RandomGenerator rng = new tlc2.util.RandomGenerator();
		final long seed = request.has("seed") ? request.get("seed").getAsLong() : rng.nextLong();
		rng.setSeed(seed);
		try {
			TLCGlobals.setNumWorkers(workers);
			TLCGlobals.coverageInterval = -1;
			FP64.Init(0);
			tlc2.value.RandomEnumerableValues.setSeed(seed);
			metadir = FileUtil.makeMetaDir(new Date(openedAt), specDir, null);
			tool = new FastTool(mainFile, config, new SimpleFilenameToStream(specDir), Tool.Mode.Simulation,
					new HashMap<>());
			runTool = tool;
			// A non-null traceActions sizes the per-worker action-pair counters;
			// anything but BASIC/FULL keeps TLC from writing its dot files.
			simulator = new tlc2.tool.Simulator(tool, metadir, null, deadlock, depth, traces, "STATS", rng, seed,
					new SimpleFilenameToStream(specDir), workers);
			TLCGlobals.simulator = simulator;
		} catch (final Throwable t) {
			tool = null;
			runTool = null;
			simulator = null;
			final JsonObject reply = error(null, "open_failed", t.toString());
			reply.add("messages", recorder.drainMessages());
			return reply;
		}
		final JsonObject reply = ok();
		reply.addProperty("mode", "simulate");
		reply.addProperty("spec", specFile.getPath());
		reply.addProperty("root_module", tool.getRootName());
		reply.addProperty("metadir", metadir);
		reply.addProperty("workers", workers);
		reply.addProperty("depth", depth);
		reply.addProperty("traces", traces == Long.MAX_VALUE ? null : traces);
		reply.addProperty("seed", seed);
		reply.addProperty("extended_statistics", tlc2.tool.Simulator.EXTENDED_STATISTICS);
		reply.add("catalogue", catalogue());
		reply.add("messages", recorder.drainMessages());
		return reply;
	}

	/**
	 * Run random behaviours until {@code traces} of them, a violation, or
	 * {@code budget_ms}; then report what the recorder saw, the simulator's
	 * statistics and the action-pair follow matrix. A run that found nothing
	 * proves nothing: the verdict says so.
	 */
	private JsonObject simulate(final JsonObject request) throws InterruptedException {
		if (simulator == null) {
			return error(null, "not_simulating", "open with mode simulate first");
		}
		final long budgetMs = request.has("budget_ms") ? request.get("budget_ms").getAsLong() : 60_000L;
		final long started = System.currentTimeMillis();
		if (simulationStoppedByBudget) {
			// Simulator.stop() is final: there is nothing to resume, so the
			// stopped run is reported again rather than as a completed one.
			final JsonObject reply = simulationReply(true);
			reply.addProperty("resumable", false);
			return reply;
		}
		if (simulatorThread == null) {
			simulatorThread = new Thread(() -> {
				try {
					simulatorResult = simulator.simulate();
				} catch (final Throwable t) {
					simulatorFailure = t;
				}
			}, "tlc-resident-simulator");
			simulatorThread.setDaemon(true);
			simulatorThread.start();
		}
		boolean stopped = false;
		while (simulatorThread.isAlive()) {
			if (System.currentTimeMillis() - started >= budgetMs) {
				simulator.stop();
				stopped = true;
				simulationStoppedByBudget = true;
				simulatorThread.join(10_000);
				break;
			}
			simulatorThread.join(20);
		}
		simulationMs += System.currentTimeMillis() - started;
		return simulationReply(stopped);
	}

	private JsonObject simulationReply(final boolean stopped) {
		final JsonObject reply = ok();
		final boolean finished = !simulatorThread.isAlive();
		reply.addProperty("finished", finished);
		reply.addProperty("stopped_by_budget", stopped);
		final int outcome = recorder.outcome();
		final Integer code = simulatorResult;
		if (finished && code != null) {
			reply.addProperty("result_code", code);
		}
		if (simulatorFailure != null) {
			reply.addProperty("verdict", "error");
			reply.addProperty("error", simulatorFailure.toString());
		} else if (outcome != EC.NO_ERROR) {
			reply.addProperty("verdict", verdict(EC.GENERAL, outcome));
		} else if (finished && !simulationStoppedByBudget && code != null && code != EC.NO_ERROR) {
			// The simulator ended on an error no violation code reports (the
			// next-state relation failing to evaluate): an error, not a clean run.
			reply.addProperty("verdict", "error");
		} else {
			reply.addProperty("verdict", "no_violation_found");
		}
		final String property = recorder.outcomeProperty();
		if (property != null) {
			reply.addProperty("violated", property);
		}
		// No store in simulation: an initial state's violation keeps TLC's text.
		recorder.completeInitial(null);
		// The last complete behaviour TLC printed, as `check` reports it:
		// an evaluation error's behaviour opens no violation trace.
		final Recorder.Trace trace = recorder.trace();
		if (trace != null) {
			reply.add("trace", traceJson(trace));
		}
		final JsonArray all = new JsonArray();
		for (final Recorder.Trace t : recorder.traces()) {
			all.add(traceJson(t));
		}
		reply.add("traces", all);
		try {
			reply.add("statistics", Recorder.value(simulator.getStatistics(null)));
		} catch (final Throwable t) {
			reply.addProperty("statistics_error", t.toString());
		}
		try {
			reply.add("action_flow", simulator.actionFlowAsJson());
		} catch (final Throwable t) {
			reply.addProperty("action_flow_error", t.toString());
		}
		reply.addProperty("simulation_ms", simulationMs);
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
		// State-level PROPERTY formulas: checked on the initial states only.
		c.add("implied_inits", names(tool.getImpliedInitNames()));
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
		if (refreshed) {
			return error(null, "refreshed",
					"this session was refreshed incrementally: its store is current and the store queries serve it, but TLC's own checker is not; open a new session for a full run");
		}
		final long budgetMs = request.has("budget_ms") ? request.get("budget_ms").getAsLong() : Long.MAX_VALUE;
		final long budgetStates = request.has("budget_states") ? request.get("budget_states").getAsLong()
				: Long.MAX_VALUE;
		final long distinctAtStart = checker.getDistinctStatesGenerated();
		final long started = System.currentTimeMillis();
		// Traces per violated property under continuation (default 1: the
		// first counterexample of each; later violations are counted only).
		// Regenerating a trace re-runs the next-state relation from an initial
		// state, which dominates a run whose invariant fails on most states.
		TLCGlobals.continuationTraceLimit = request.has("traces_per_property")
				? request.get("traces_per_property").getAsInt()
				: 1;
		if (checkerThread == null) {
			// The cap is per run: a resumed run keeps its count, so a later
			// call does not print another trace for a property already traced.
			TLCGlobals.resetContinuationTraces();
		}

		if (resultCode == null && checkerFailure == null) {
			if (request.has("continue")) {
				// Keep exploring past a violation, so one run reports every
				// invariant's verdict. Process-global, as TLC's -continue is,
				// and set only for a run that is about to explore: an ended
				// run keeps the value it ran under.
				TLCGlobals.continuation = request.get("continue").getAsBoolean();
			}
			runContinuation = TLCGlobals.continuation;
			everContinued |= runContinuation;
			if (checkerThread == null) {
				checkerThread = new Thread(() -> {
					try {
						resultCode = checker.modelCheck();
					} catch (final Throwable t) {
						checkerFailure = t;
					} finally {
						// A run that ends before any worker starts (an
						// initial state violates an invariant, init fails to
						// evaluate) never finishes the queue, so a budget
						// suspend waiting for the workers would wait forever.
						// Finishing it wakes that wait; after a run that
						// reached the workers it is already finished.
						checker.theStateQueue.finishAll();
					}
				}, "tlc-resident-checker");
				checkerThread.setDaemon(true);
				checkerThread.start();
			} else {
				checker.resume();
			}
			// Wait for the run to end or the budget to run out. The queue's
			// suspend blocks until every worker has parked, so on return the
			// counters are quiescent. The initial states are generated before
			// any worker runs and cannot be paused: a budget that runs out
			// then takes effect once they are done (or the run has ended).
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
		recorder.completeInitial(initialStates());
		final Recorder.Trace trace = recorder.trace();
		if (trace != null) {
			reply.add("trace", traceJson(trace));
		}
		// Under the per-property trace cap a violation past the cap is
		// reported (and counted in the verdicts) but carries no states;
		// those entries are not listed as traces.
		final JsonArray all = new JsonArray();
		for (final Recorder.Trace t : recorder.traces()) {
			if (!t.states.isEmpty()) {
				all.add(traceJson(t));
			}
		}
		reply.add("traces", all);
		// Reports past the cap are counted here instead of listed as messages.
		reply.add("untraced_reports", recorder.untracedReports());
		reply.add("invariants", invariantVerdicts(finished));
		reply.addProperty("continuation", runContinuation);
		reply.add("stats", stats());
		reply.add("messages", recorder.drainMessages());
		return reply;
	}

	/**
	 * Maps the text TLC printed an initial state as, in a report of a
	 * violation there, to that state from the store: every initial state is
	 * stored before TLC checks it, those a constraint excludes included. The
	 * text is matched against each stored initial state printed as TLC
	 * printed it (through the ALIAS, if any), so the match is TLC's own
	 * state. Null without a store; the recorder then keeps the text.
	 */
	private java.util.function.Function<String, JsonObject> initialStates() {
		if (store == null) {
			return null;
		}
		final Map<String, TLCState> byText = new HashMap<>();
		return text -> {
			if (byText.isEmpty()) {
				final long[] in = store.initialFingerprints();
				final long[] ex = store.excludedInitialFingerprints();
				final long[] all = java.util.Arrays.copyOf(in, in.length + ex.length);
				System.arraycopy(ex, 0, all, in.length, ex.length);
				for (final long fp : all) {
					final TLCState s = store.read(fp);
					if (s == null) {
						continue;
					}
					try {
						byText.putIfAbsent(tool.evalAlias(s, s).toString(), s);
					} catch (final RuntimeException e) {
						// An ALIAS that does not evaluate here: that state keeps its text.
					}
				}
			}
			final TLCState s = byText.get(text);
			return s == null ? null : Recorder.state(s);
		};
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
		final Map<String, String> failures = recorder.evaluationFailures();
		final List<Recorder.Trace> traces = recorder.traces();
		final boolean exhausted = finished && explorationComplete();
		// Under continuation TLC reports the first invariant a state violates
		// and checks no further invariant on that state. An invariant never
		// reported may then fail only on states an earlier one failed on, so
		// its silence is no verdict: it is evaluated over the stored graph.
		final java.util.Set<String> unreported = new java.util.LinkedHashSet<>();
		boolean anyViolated = false;
		for (final String name : tool.getInvNames()) {
			if (counts.containsKey(name)) {
				anyViolated = true;
			} else if (!failures.containsKey(name)) {
				unreported.add(name);
			}
		}
		// Any part of the run under continuation, not only its last call: a
		// run resumed without it keeps the states it already skipped past.
		final boolean skipped = exhausted && everContinued && anyViolated && !unreported.isEmpty();
		final Map<String, Incremental.Sweep> swept = new HashMap<>();
		if (skipped && store != null) {
			for (final Incremental.Sweep sw : Incremental.sweep(tool, store, unreported)) {
				if (unreported.contains(sw.invariant)) {
					swept.put(sw.invariant, sw);
				}
			}
		}
		for (final String name : tool.getInvNames()) {
			final JsonObject v = new JsonObject();
			v.addProperty("name", name);
			final Integer n = counts.get(name);
			final String failure = failures.get(name);
			if (n != null || failure != null) {
				if (n != null) {
					v.addProperty("verdict", "violated");
					v.addProperty("reports", n);
				} else {
					// It did not evaluate on some state: no verdict either way.
					v.addProperty("verdict", "not_evaluable");
				}
				if (failure != null) {
					v.addProperty("error", failure);
				}
				// The first trace of the verdict's own kind.
				final boolean violation = n != null;
				for (final Recorder.Trace t : traces) {
					if (name.equals(t.property)
							&& violation == (t.code != EC.TLC_INVARIANT_EVALUATION_FAILED)) {
						v.addProperty("level", t.states.size());
						if (!t.states.isEmpty()) {
							v.add("action", t.states.get(t.states.size() - 1).get("action"));
						}
						break;
					}
				}
			} else if (skipped) {
				final Incremental.Sweep sw = swept.get(name);
				if (sw == null) {
					v.addProperty("verdict", "not_evaluated");
					v.addProperty("reason",
							"under continuation TLC checks no further invariant on a state that violates one, and without a store the skipped states cannot be revisited");
				} else if (sw.error != null) {
					v.addProperty("verdict", "not_evaluable");
					v.addProperty("error", sw.error);
				} else if (sw.violations > 0) {
					// Found over the store, not reported by TLC: no trace.
					v.addProperty("verdict", "violated");
					v.addProperty("reports", sw.violations);
					v.addProperty("level", sw.firstLevel);
					v.addProperty("fp", sw.firstFp);
					v.addProperty("source", "store");
				} else {
					v.addProperty("verdict", "no_violation_found");
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
		case EC.TLC_PROPERTY_VIOLATED_INITIAL:
			// A PROPERTY that is false in an initial state.
			return "property_violated";
		case EC.TLC_DEADLOCK_REACHED:
			return "deadlock";
		case EC.TLC_INVARIANT_EVALUATION_FAILED:
			return "evaluation_failed";
		default:
			return code == EC.NO_ERROR ? "ok" : "error";
		}
	}

	/**
	 * Whether the checker explored the whole reachable graph: it ended on its
	 * own with nothing left in its queue, and on a code that never cuts a
	 * state's expansion short. A deadlock is found after the state's (empty)
	 * expansion and a temporal violation after the graph is complete; an
	 * invariant or action-property violation aborts the expansion it occurs
	 * in unless TLC continues past violations. Any other error may have.
	 */
	private boolean explorationComplete() {
		if (checkerThread == null || checkerThread.isAlive() || checkerFailure != null || resultCode == null
				|| checker.getStateQueueSize() != 0) {
			return false;
		}
		switch (resultCode) {
		case EC.NO_ERROR:
		case EC.TLC_DEADLOCK_REACHED:
		case EC.TLC_TEMPORAL_PROPERTY_VIOLATED:
			return true;
		case EC.TLC_INVARIANT_VIOLATED_INITIAL:
		case EC.TLC_INVARIANT_VIOLATED_BEHAVIOR:
		case EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR:
			return runContinuation;
		default:
			return false;
		}
	}

	/** Whether a result code reports a property violated (or a deadlock), not an error. */
	private static boolean isViolation(final int code) {
		switch (code) {
		case EC.TLC_INVARIANT_VIOLATED_INITIAL:
		case EC.TLC_INVARIANT_VIOLATED_BEHAVIOR:
		case EC.TLC_INVARIANT_VIOLATED_LEVEL:
		case EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR:
		case EC.TLC_TEMPORAL_PROPERTY_VIOLATED:
		case EC.TLC_PROPERTY_VIOLATED_INITIAL:
		case EC.TLC_DEADLOCK_REACHED:
			return true;
		default:
			return false;
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
		s.add("store", storeInfo());
		return s;
	}

	/**
	 * The counters TLC keeps beyond the headline statistics: whether the
	 * reachable graph was exhausted and what stopped the run, the workers'
	 * out-degree distribution (bucketed, the top bucket saturating at 32),
	 * the fingerprint set's own statistics, the fingerprint-collision
	 * probability, and the liveness checkers in play.
	 */
	private JsonObject registers() {
		final JsonObject r = new JsonObject();
		final boolean finished = resultCode != null;
		// The same judgement a refresh relies on: an error (an invariant or
		// the next-state relation failing to evaluate) ends the run with
		// states unexplored, continuation or not.
		final boolean exhausted = finished && explorationComplete();
		r.addProperty("finished", finished);
		r.addProperty("exhausted", exhausted);
		r.addProperty("stopped_by", checkerFailure != null ? "error"
				: !finished ? (checkerThread == null ? "not_started" : "budget")
				// Under continuation a run that reported violations still ends
				// on NO_ERROR, so the recorder, not the code, says if it found any.
				: exhausted ? (resultCode == EC.NO_ERROR && recorder.violationCounts().isEmpty() ? "exhausted"
						: "exhausted_with_violations")
				: isViolation(resultCode) ? "violation" : "error");
		if (finished) {
			r.addProperty("result_code", resultCode);
		}
		r.addProperty("workers", TLCGlobals.getNumWorkers());
		r.addProperty("continuation", runContinuation);
		r.addProperty("coverage", tlc2.tool.coverage.CoverageWalk.enabled());
		// Out-degree across workers.
		final JsonObject outDegree = new JsonObject();
		long observations = 0;
		int min = Integer.MAX_VALUE;
		int max = -1;
		double weightedMean = 0;
		final java.util.TreeMap<Integer, Long> samples = new java.util.TreeMap<>();
		for (final tlc2.tool.IWorker w : checker.getWorkers()) {
			if (!(w instanceof tlc2.tool.Worker)) {
				continue;
			}
			final tlc2.util.statistics.IBucketStatistics b = ((tlc2.tool.Worker) w).getOutDegree();
			if (b == null || b.getObservations() == 0) {
				continue;
			}
			observations += b.getObservations();
			min = Math.min(min, b.getMin());
			max = Math.max(max, b.getMax());
			weightedMean += b.getMean() * b.getObservations();
			b.getSamples().forEach((k, v) -> samples.merge(k, v, Long::sum));
		}
		if (observations > 0) {
			outDegree.addProperty("observations", observations);
			outDegree.addProperty("min", min);
			outDegree.addProperty("max", max);
			outDegree.addProperty("mean", weightedMean / observations);
			outDegree.addProperty("saturated_at", 32);
			final JsonObject buckets = new JsonObject();
			samples.forEach((k, v) -> buckets.addProperty(String.valueOf(k), v));
			outDegree.add("buckets", buckets);
		}
		r.add("out_degree", outDegree);
		// The fingerprint set.
		final JsonObject fpset = new JsonObject();
		fpset.addProperty("implementation", checker.theFPSet.getClass().getSimpleName());
		if (checker.theFPSet instanceof tlc2.tool.fp.FPSetStatistic) {
			final tlc2.tool.fp.FPSetStatistic f = (tlc2.tool.fp.FPSetStatistic) checker.theFPSet;
			try {
				fpset.addProperty("table_count", f.getTblCnt());
				fpset.addProperty("disk_lookups", f.getDiskLookupCnt());
				fpset.addProperty("memory_hits", f.getMemHitCnt());
				fpset.addProperty("disk_hits", f.getDiskHitCnt());
				fpset.addProperty("disk_writes", f.getDiskWriteCnt());
				fpset.addProperty("flush_time_ms", f.getFlushTime());
				fpset.addProperty("bytes", f.sizeof());
			} catch (final RuntimeException e) {
				fpset.addProperty("error", e.toString());
			}
		}
		r.add("fpset", fpset);
		final long generated = checker.getStatesGenerated();
		final long distinct = checker.getDistinctStatesGenerated();
		if (distinct > 0 && generated > 0) {
			r.addProperty("fp_collision_probability",
					tlc2.tool.AbstractChecker.calculateOptimisticProbability(distinct, generated));
		}
		// Liveness.
		final JsonObject liveness = new JsonObject();
		liveness.addProperty("enabled", TLCGlobals.doLiveness());
		liveness.addProperty("temporal_properties", tool.getTemporals().length);
		r.add("liveness", liveness);
		return r;
	}

	private JsonObject storeInfo() {
		final JsonObject o = new JsonObject();
		if (store == null) {
			return o;
		}
		o.addProperty("states", store.states());
		o.addProperty("initial", store.initialStates());
		o.addProperty("edges", store.edges());
		o.addProperty("unsatisfied", store.unsatisfied());
		o.addProperty("excluded", store.excluded());
		o.addProperty("excluded_states", store.excludedStates());
		o.addProperty("bytes", store.bytes());
		return o;
	}

	// ─── the store's queries ────────────────────────────────────────────

	private JsonObject notOpen() {
		if (tool != null && !storing) {
			return error(null, "no_store", "this session was opened with store: false; reopen with the store to query it");
		}
		return error(null, "not_open", "open a spec first");
	}

	private static Long fpOf(final JsonObject request, final String key) {
		if (!request.has(key) || request.get(key).isJsonNull()) {
			return null;
		}
		final JsonElement e = request.get(key);
		try {
			return e.getAsJsonPrimitive().isNumber() ? e.getAsLong() : Long.parseLong(e.getAsString());
		} catch (final RuntimeException ex) {
			return null;
		}
	}

	private String actionName(final long id) {
		final Action a = store.action((int) id);
		return a == null ? (id < 0 ? "<Initial predicate>" : "action#" + id) : a.getNameOfDefault();
	}

	/**
	 * Re-parse the spec after an edit and re-explore only what the edit
	 * reaches (see {@link Incremental}). A change to the variables, the
	 * initial predicate, a constraint or the config, a VIEW or SYMMETRY set,
	 * a spec that reads {@code TLCGet}, or a first run that did not
	 * finish, leaves nothing to carry:
	 * the reply asks for a restart and a full run.
	 *
	 * <p>
	 * The replay starts from the last fully explored graph ({@link #baseStore}),
	 * not necessarily the current store: a refresh cut short by its budget or
	 * a first violation is served to the store queries but not replayed from.
	 * A replay that fails (the edited spec does not evaluate) is not adopted:
	 * the current tool and store stay. Neither is one whose assumptions fail:
	 * TLC would not explore it. State-level {@code PROPERTY} formulas are
	 * checked on the initial states, as TLC checks them.
	 *
	 * <p>
	 * A paused checker is left parked, not stopped: stopping ends its run as
	 * if it had finished. Parsing the edited spec rebinds TLC's static
	 * variable tables, so when the new tool is not adopted they are rebound
	 * to the old one, and the parked run may resume only if that is exact.
	 */
	private JsonObject refresh(final JsonObject request) throws Exception {
		if (simulator != null) {
			return error(null, "not_checking",
					"refresh replays a model-checking store; a simulate session has none. Open a new session");
		}
		if (tool == null) {
			return notOpen();
		}
		final long budgetMs = request.has("budget_ms") ? request.get("budget_ms").getAsLong() : 60_000L;
		final boolean cont = request.has("continue") && request.get("continue").getAsBoolean();
		final long started = System.currentTimeMillis();
		recorder.drainMessages();
		// Decided before parsing, so these paths leave TLC's statics alone.
		final String currentConfig = readConfig();
		String before = null;
		if (!storing) {
			before = "the session was opened without a store, so there is no graph to replay";
		} else if (currentConfig == null || !currentConfig.equals(configText)) {
			before = "the model config changed";
		} else if (!refreshed && !explorationComplete()) {
			before = "the previous exploration did not finish, so the store is not the whole graph";
		}
		if (before != null) {
			return fullRerun(ok(), before, started);
		}
		if (baseStore == null) {
			// The first refresh, from a run that explored the whole graph.
			baseTool = tool;
			baseStore = store;
		}
		// Parsing rebinds the process-global name slots; kept to put them back
		// if the edited spec is not adopted.
		final Map<util.UniqueString, Integer> slots = nameSlots();
		final Tool newTool;
		try {
			newTool = new FastTool(mainFile, configName, new SimpleFilenameToStream(specDir), Tool.Mode.MC,
					new HashMap<>());
		} catch (final Throwable t) {
			final JsonObject reply = error(null, "parse_failed", t.toString());
			reply.add("messages", recorder.drainMessages());
			// The current tool and store stay in place.
			rebindStatics(tool, slots);
			return reply;
		}
		final Incremental.ActionDiff diff = Incremental.diff(baseTool, newTool);
		final JsonObject reply = ok();
		reply.add("diff", Incremental.diffJson(diff));
		reply.addProperty("front_end_ms", System.currentTimeMillis() - started);
		if (diff.fullRerunReason != null) {
			rebindStatics(tool, slots);
			return fullRerun(reply, diff.fullRerunReason, started);
		}
		reply.addProperty("mode", "incremental");
		// TLC checks the assumptions before it explores anything; an edited
		// ASSUME is checked here too, since the constants it constrains are
		// the config's and a refresh never runs the checker's own check.
		final int assumptions = newTool.checkAssumptions();
		if (assumptions != EC.NO_ERROR) {
			rebindStatics(tool, slots);
			reply.addProperty("adopted", false);
			reply.addProperty("finished", false);
			reply.addProperty("complete", false);
			reply.addProperty("verdict",
					assumptions == EC.TLC_ASSUMPTION_FALSE ? "assumption_false" : "assumption_evaluation_failed");
			reply.addProperty("error", assumptions == EC.TLC_ASSUMPTION_FALSE
					? "an assumption of the edited spec is false; the messages name it"
					: "an assumption of the edited spec did not evaluate; the messages say why");
			reply.addProperty("duration_ms", System.currentTimeMillis() - started);
			reply.add("store", storeInfo());
			reply.add("messages", recorder.drainMessages());
			return reply;
		}
		reply.addProperty("assumptions", "hold");
		reply.addProperty("replayed_from", baseStore == store ? "current" : "last_complete");
		final String newMetadir = FileUtil.makeMetaDir(new Date(System.currentTimeMillis()), specDir, null);
		final GraphStore newStore = new GraphStore(newMetadir);
		Incremental.Result r;
		try {
			r = Incremental.replay(newTool, baseStore, newStore, diff, budgetMs, cont);
		} catch (final Throwable t) {
			// Anything the replay did not turn into an error of its own still
			// leaves the edited spec unadopted, and is cleaned up below.
			r = new Incremental.Result();
			r.error = t.toString();
		}
		reply.addProperty("survivors", r.survivors);
		reply.addProperty("dropped", r.dropped);
		reply.addProperty("reexpanded", r.reexpanded);
		reply.addProperty("new_states", r.newStates);
		reply.addProperty("edges_copied", r.edgesCopied);
		reply.addProperty("edges_generated", r.edgesGenerated);
		reply.addProperty("budget_exhausted", r.budgetExhausted);
		if (r.error != null) {
			// The edited spec does not evaluate; keep serving what was there.
			newStore.dispose();
			rebindStatics(tool, slots);
			reply.addProperty("adopted", false);
			reply.addProperty("finished", false);
			reply.addProperty("complete", false);
			reply.addProperty("error", r.error);
			reply.addProperty("duration_ms", System.currentTimeMillis() - started);
			reply.add("store", storeInfo());
			reply.add("messages", recorder.drainMessages());
			return reply;
		}
		final GraphStore previous = store;
		tool = newTool;
		store = newStore;
		metadir = newMetadir;
		refreshed = true;
		// Only a replay that ran to the end holds the whole graph: one cut
		// by its budget or a first violation leaves states whose successors
		// were never generated. Such a store is served, not replayed from.
		final boolean stoppedAtViolation = !cont && !r.violations.isEmpty();
		final boolean complete = !r.budgetExhausted && !stoppedAtViolation;
		refreshComplete = complete;
		if (complete) {
			final GraphStore oldBase = baseStore;
			baseTool = newTool;
			baseStore = newStore;
			retire(oldBase);
		}
		retire(previous);
		reply.addProperty("adopted", true);
		reply.addProperty("finished", !r.budgetExhausted);
		reply.addProperty("complete", complete);
		reply.addProperty("stopped_at_first_violation", stoppedAtViolation);
		final JsonArray violations = new JsonArray();
		for (final Incremental.Violation v : r.violations) {
			final JsonObject o = new JsonObject();
			o.addProperty("invariant", v.invariant);
			o.addProperty("fp", v.fp);
			o.addProperty("level", v.level);
			violations.add(o);
		}
		// Per-invariant verdicts: exact over the refreshed store when the
		// replay explored the whole graph (one evaluation per state and
		// invariant), else not_evaluated.
		final JsonArray invs = new JsonArray();
		if (complete) {
			final JsonArray exact = new JsonArray();
			for (final Incremental.Sweep sw : Incremental.sweep(tool, store)) {
				final JsonObject v = new JsonObject();
				v.addProperty("name", sw.invariant);
				if (sw.error != null) {
					v.addProperty("verdict", "not_evaluable");
					v.addProperty("error", sw.error);
				} else if (sw.violations > 0) {
					v.addProperty("verdict", "violated");
					v.addProperty("reports", sw.violations);
					v.addProperty("level", sw.firstLevel);
					v.addProperty("fp", sw.firstFp);
					final JsonObject o = new JsonObject();
					o.addProperty("invariant", sw.invariant);
					o.addProperty("fp", sw.firstFp);
					o.addProperty("level", sw.firstLevel);
					o.addProperty("count", sw.violations);
					exact.add(o);
				} else {
					v.addProperty("verdict", "no_violation_found");
				}
				invs.add(v);
			}
			reply.add("violations", exact);
		} else {
			for (final String name : tool.getInvNames()) {
				final JsonObject v = new JsonObject();
				v.addProperty("name", name);
				Incremental.Violation first = null;
				for (final Incremental.Violation x : r.violations) {
					if (x.invariant.equals(name)) {
						first = x;
						break;
					}
				}
				if (first != null) {
					v.addProperty("verdict", "violated");
					v.addProperty("level", first.level);
					v.addProperty("fp", first.fp);
				} else {
					v.addProperty("verdict", "not_evaluated");
				}
				invs.add(v);
			}
			reply.add("violations", violations);
		}
		reply.add("invariants", invs);
		// State-level PROPERTY formulas, which TLC checks on the initial
		// states only. The initial predicate is unchanged, so every initial
		// state is in the refreshed store, whatever stopped the replay.
		final JsonArray props = new JsonArray();
		for (final Incremental.Sweep sw : Incremental.impliedInits(tool, store)) {
			final JsonObject v = new JsonObject();
			v.addProperty("name", sw.invariant);
			if (sw.error != null) {
				v.addProperty("verdict", "not_evaluable");
				v.addProperty("error", sw.error);
			} else if (sw.violations > 0) {
				v.addProperty("verdict", "violated_initially");
				v.addProperty("reports", sw.violations);
				v.addProperty("fp", sw.firstFp);
			} else {
				v.addProperty("verdict", "no_violation_found");
			}
			props.add(v);
		}
		reply.add("implied_inits", props);
		reply.add("unchecked", unchecked());
		reply.addProperty("duration_ms", System.currentTimeMillis() - started);
		reply.add("store", storeInfo());
		reply.add("messages", recorder.drainMessages());
		return reply;
	}

	/**
	 * What a refresh does not recheck, so a caller does not read the
	 * invariant verdicts as the whole answer (it does check the assumptions
	 * and the state-level properties, under {@code implied_inits}): temporal properties (the
	 * liveness tableau is not rebuilt), implied actions, deadlock, and the
	 * blocked-guard tallies (not recorded during a replay).
	 */
	private JsonObject unchecked() {
		final JsonObject o = new JsonObject();
		final JsonArray temporals = new JsonArray();
		for (final Action a : tool.getTemporals()) {
			temporals.add(a.getNameOfDefault());
		}
		for (final Action a : tool.getImpliedTemporals()) {
			temporals.add(a.getNameOfDefault());
		}
		o.add("temporal_properties", temporals);
		o.add("implied_actions", names(tool.getImpliedActNames()));
		o.addProperty("deadlock", checkDeadlock);
		o.addProperty("guard_tallies", true);
		return o;
	}

	/**
	 * After an incremental refresh the checker's counters and registers
	 * describe the run before it, not the refreshed store: say so, and say
	 * whether the store now holds the whole graph, as the refresh reported.
	 */
	private void markStale(final JsonObject reply) {
		if (!refreshed) {
			return;
		}
		reply.addProperty("stale", true);
		reply.addProperty("stale_reason",
				"the store was refreshed incrementally; the counters and registers are the last full run's, over the spec as it was then (only `store` is current)");
		reply.addProperty("refresh_complete", refreshComplete);
	}

	/** Release a store nothing refers to any more. */
	private void retire(final GraphStore s) {
		if (s != null && s != store && s != baseStore) {
			s.dispose();
		}
	}

	/**
	 * Nothing can be carried. A second checker in this JVM trips over TLC's
	 * per-process state (worker and trace bookkeeping), so the caller
	 * restarts the resident for the full run; the old tool and store stay in
	 * place until then.
	 */
	private JsonObject fullRerun(final JsonObject reply, final String reason, final long started) {
		reply.addProperty("mode", "full");
		reply.addProperty("restart_required", true);
		reply.addProperty("reason", reason);
		reply.addProperty("duration_ms", System.currentTimeMillis() - started);
		reply.add("messages", recorder.drainMessages());
		return reply;
	}

	/** The model config's text, or null when it cannot be read. */
	private String readConfig() {
		try {
			return new String(java.nio.file.Files.readAllBytes(new File(specDir, configName + ".cfg").toPath()),
					StandardCharsets.UTF_8);
		} catch (final IOException e) {
			return null;
		}
	}

	/**
	 * Rebind TLC's static variable tables to {@code old} after parsing a spec
	 * that was not adopted. Parsing assigns each variable name its slot and
	 * sets the variable count, the empty state and the state's tool; this
	 * puts the old spec's back, and every name's slot as {@code slots}
	 * recorded it before the parse (a definition of the old spec that the
	 * new one declares a variable would otherwise evaluate as that
	 * variable). Should a definition still read as a variable, nothing that
	 * evaluates against the spec is served any more.
	 */
	private void rebindStatics(final Tool old, final Map<util.UniqueString, Integer> slots) {
		// Every name's slot as it was before the parse: a definition of the
		// old spec that the edited one declares a variable gets its definition
		// slot back. A name first seen in the parse gets none.
		for (final util.UniqueString u : util.UniqueString.internTbl.toMap().values()) {
			final Integer loc = slots.get(u);
			u.setLoc(loc == null ? -1 : loc);
		}
		final tla2sany.semantic.OpDeclNode[] vars = old.getSpecProcessor().getVariablesNodes();
		for (int i = 0; i < vars.length; i++) {
			vars[i].getName().setLoc(i);
		}
		util.UniqueString.setVariableCount(vars.length);
		tlc2.tool.TLCStateMut.setVariables(vars);
		tlc2.tool.TLCStateMut.setTool(old);
		final OpDefNode[] defs = old.getSpecProcessor().getRootModule().getOpDefs();
		for (final OpDefNode def : defs == null ? new OpDefNode[0] : defs) {
			if (def.getName().getVarLoc() >= 0) {
				restartRequired = "parsing the edited spec reassigned the definition " + def.getName();
				return;
			}
		}
	}

	/** Every interned name's slot in a state or the definition table (-1 for none). */
	private static Map<util.UniqueString, Integer> nameSlots() {
		final Map<util.UniqueString, Integer> out = new java.util.IdentityHashMap<>();
		for (final util.UniqueString u : util.UniqueString.internTbl.toMap().values()) {
			// A slot is either a variable's or a definition's.
			out.put(u, Math.max(u.getVarLoc(), u.getDefnLoc()));
		}
		return out;
	}

	/**
	 * The refusal every request that evaluates against the spec gives once a
	 * refresh left TLC's statics unfit for it, or null.
	 */
	private JsonObject restartRefusal() {
		if (restartRequired == null) {
			return null;
		}
		return error(null, "restart_required",
				"this session cannot evaluate against its spec any more: " + restartRequired + "; open a new session");
	}

	/** The path from an initial state to a stored fingerprint. */
	private JsonObject trace(final JsonObject request) {
		if (store == null) {
			return notOpen();
		}
		final Long fp = fpOf(request, "fp");
		if (fp == null) {
			return error(null, "invalid_request", "trace needs `fp`, a stored fingerprint");
		}
		final long[][] path = store.pathTo(fp);
		if (path == null) {
			return error(null, "unknown_state", "no stored state with fingerprint " + fp);
		}
		final JsonArray states = new JsonArray();
		for (int i = 0; i < path.length; i++) {
			final TLCState state = store.read(path[i][0]);
			final JsonObject s = state == null ? new JsonObject() : Recorder.state(state);
			s.addProperty("ordinal", i + 1);
			s.addProperty("fp", path[i][0]);
			s.addProperty("action", actionName(path[i][1]));
			states.add(s);
		}
		final JsonObject reply = ok();
		reply.addProperty("fp", fp);
		reply.addProperty("length", path.length);
		reply.addProperty("shortest", TLCGlobals.getNumWorkers() == 1);
		reply.add("states", states);
		return reply;
	}

	/** Recorded predecessors of a stored state and, freshly computed, its successors per action. */
	private JsonObject neighbours(final JsonObject request) {
		if (store == null) {
			return notOpen();
		}
		final Long fp = fpOf(request, "fp");
		if (fp == null) {
			return error(null, "invalid_request", "neighbours needs `fp`, a stored fingerprint");
		}
		final TLCState state = store.read(fp);
		if (state == null) {
			return error(null, "unknown_state", "no stored state with fingerprint " + fp);
		}
		final JsonObject reply = ok();
		reply.addProperty("fp", fp);
		reply.addProperty("level", store.level(fp));
		reply.add("state", Recorder.state(state));
		final JsonArray preds = new JsonArray();
		for (final long[] p : store.predecessorsOf(fp)) {
			final JsonObject o = new JsonObject();
			o.addProperty("fp", p[0]);
			o.addProperty("action", actionName(p[1]));
			o.addProperty("action_id", p[1]);
			o.addProperty("seen_before", (p[2] & tlc2.util.IStateWriter.IsSeen) != 0);
			preds.add(o);
		}
		reply.add("predecessors", preds);
		final JsonArray succs = new JsonArray();
		int enabled = 0;
		for (final Action a : tool.getActions()) {
			final JsonObject o = new JsonObject();
			o.addProperty("action", a.getNameOfDefault());
			o.addProperty("action_id", a.getId());
			try {
				// Not counted in the run's coverage: this query is not part of the run.
				final StateVec next = tool.getNextStatesUnrecorded(a, state);
				o.addProperty("enabled", next.size() > 0);
				o.addProperty("successors", next.size());
				if (next.size() > 0) {
					enabled++;
				}
				final JsonArray fps = new JsonArray();
				for (int i = 0; i < next.size(); i++) {
					final TLCState succ = next.elementAt(i);
					final JsonObject so = new JsonObject();
					long sfp = 0;
					try {
						sfp = succ.fingerPrint();
					} catch (final RuntimeException e) {
						so.addProperty("unassigned", true);
					}
					so.addProperty("fp", sfp);
					so.addProperty("stored", store.contains(sfp));
					so.add("changed", changed(state, succ));
					fps.add(so);
				}
				o.add("states", fps);
			} catch (final Throwable t) {
				o.addProperty("enabled", (Boolean) null);
				o.addProperty("error", t.toString());
			}
			succs.add(o);
		}
		reply.addProperty("enabled_actions", enabled);
		reply.add("successors", succs);
		return reply;
	}

	/** The variables whose values differ between two states. */
	private static JsonArray changed(final TLCState a, final TLCState b) {
		final JsonArray out = new JsonArray();
		final Map<util.UniqueString, IValue> va = a.getVals();
		final Map<util.UniqueString, IValue> vb = b.getVals();
		if (va == null || vb == null) {
			return out;
		}
		for (final Map.Entry<util.UniqueString, IValue> e : vb.entrySet()) {
			final IValue before = va.get(e.getKey());
			if (before == null || !before.equals(e.getValue())) {
				out.add(e.getKey().toString());
			}
		}
		return out;
	}

	/** Parse a caller expression against the root module, as the debugger does. */
	private OpDefNode parse(final String expression) throws Exception {
		final tlc2.tool.impl.SpecProcessor proc = tool.getSpecProcessor();
		final OpDefNode def = TLCDebuggerExpression.process(proc, proc.getRootModule(), expression);
		if (def == null) {
			throw new IllegalArgumentException("could not parse expression: " + expression);
		}
		return def;
	}

	/** Evaluate an expression in a stored state, or over a stored state pair. */
	private JsonObject eval(final JsonObject request) {
		if (store == null) {
			return notOpen();
		}
		final String expression = string(request, "expr", null);
		final Long fp = fpOf(request, "fp");
		if (expression == null || fp == null) {
			return error(null, "invalid_request", "eval needs `expr` and `fp` (and optionally `fp2` for a primed expression)");
		}
		final TLCState s0 = store.read(fp);
		if (s0 == null) {
			return error(null, "unknown_state", "no stored state with fingerprint " + fp);
		}
		final Long fp2 = fpOf(request, "fp2");
		TLCState s1 = null;
		if (fp2 != null) {
			s1 = store.read(fp2);
			if (s1 == null) {
				return error(null, "unknown_state", "no stored state with fingerprint " + fp2);
			}
		}
		final JsonObject reply = ok();
		reply.addProperty("expr", expression);
		reply.addProperty("fp", fp);
		final long started = System.currentTimeMillis();
		try {
			final OpDefNode def = parse(expression);
			final IValue value = s1 == null ? tool.eval(def.getBody(), Context.Empty, s0)
					: tool.eval(def.getBody(), Context.Empty, s0, s1, EvalControl.Clear, CostModel.DO_NOT_RECORD);
			reply.addProperty("evaluated", true);
			reply.add("value", Recorder.value(value));
			reply.addProperty("tla", value.toString());
		} catch (final Throwable t) {
			reply.addProperty("evaluated", false);
			reply.addProperty("error", t.getMessage() == null ? t.toString() : t.getMessage());
		}
		reply.addProperty("duration_ms", System.currentTimeMillis() - started);
		reply.add("messages", recorder.drainMessages());
		return reply;
	}

	/** Evaluate candidate state predicates over every stored state. */
	private JsonObject screen(final JsonObject request) throws InterruptedException {
		if (store == null) {
			return notOpen();
		}
		if (!request.has("candidates") || !request.get("candidates").isJsonArray()) {
			return error(null, "invalid_request", "screen needs `candidates`, a list of state predicates");
		}
		final long budgetMs = request.has("budget_ms") ? request.get("budget_ms").getAsLong() : 60_000L;
		final JsonArray candidates = request.getAsJsonArray("candidates");
		final int n = candidates.size();
		final String[] texts = new String[n];
		final OpDefNode[] defs = new OpDefNode[n];
		final String[] errors = new String[n];
		final long[] violations = new long[n];
		final Long[] firstViolation = new Long[n];
		final long[] evaluated = new long[n];
		for (int i = 0; i < n; i++) {
			texts[i] = candidates.get(i).getAsString();
			try {
				defs[i] = parse(texts[i]);
			} catch (final Throwable t) {
				errors[i] = t.getMessage() == null ? t.toString() : t.getMessage();
			}
		}
		if (checkerThread != null && checkerThread.isAlive()) {
			checker.suspend();
		}
		final long started = System.currentTimeMillis();
		final long[] fps = store.fingerprints();
		int scanned = 0;
		boolean budgetHit = false;
		for (final long fp : fps) {
			if (System.currentTimeMillis() - started > budgetMs) {
				budgetHit = true;
				break;
			}
			final TLCState state = store.read(fp);
			if (state == null) {
				continue;
			}
			scanned++;
			for (int i = 0; i < n; i++) {
				if (defs[i] == null || errors[i] != null) {
					continue;
				}
				try {
					final IValue v = tool.eval(defs[i].getBody(), Context.Empty, state);
					evaluated[i]++;
					if (!(v instanceof BoolValue)) {
						errors[i] = "not a boolean at fingerprint " + fp + ": " + v;
					} else if (!((BoolValue) v).val) {
						violations[i]++;
						if (firstViolation[i] == null) {
							firstViolation[i] = fp;
						}
					}
				} catch (final Throwable t) {
					errors[i] = (t.getMessage() == null ? t.toString() : t.getMessage()) + " at fingerprint " + fp;
				}
			}
		}
		final JsonObject reply = ok();
		reply.addProperty("stored", fps.length);
		reply.addProperty("scanned", scanned);
		reply.addProperty("budget_exhausted", budgetHit);
		reply.addProperty("duration_ms", System.currentTimeMillis() - started);
		final JsonArray results = new JsonArray();
		for (int i = 0; i < n; i++) {
			final JsonObject r = new JsonObject();
			r.addProperty("expr", texts[i]);
			if (errors[i] != null) {
				r.addProperty("verdict", "not_evaluable");
				r.addProperty("error", errors[i]);
			} else if (violations[i] > 0) {
				r.addProperty("verdict", "violated");
				r.addProperty("violations", violations[i]);
				r.addProperty("first_violation_fp", firstViolation[i]);
				r.addProperty("first_violation_level", store.level(firstViolation[i]));
			} else {
				r.addProperty("verdict", budgetHit ? "no_violation_in_scanned" : "holds_on_stored");
			}
			r.addProperty("evaluated", evaluated[i]);
			results.add(r);
		}
		reply.add("results", results);
		reply.add("messages", recorder.drainMessages());
		return reply;
	}

	/** The guard conjuncts that kept transitions from firing, most often first. */
	private JsonObject guardProfile() {
		if (store == null) {
			return notOpen();
		}
		final JsonObject reply = ok();
		final JsonArray rows = new JsonArray();
		for (final GraphStore.Blocked b : store.blocked()) {
			final JsonObject o = new JsonObject();
			o.addProperty("action", b.action);
			o.addProperty("action_id", b.actionId);
			o.addProperty("kind", b.kind);
			o.addProperty("location", b.location);
			o.addProperty("text", b.text);
			o.addProperty("count", b.count);
			o.addProperty("example_fp", b.exampleFp);
			if (b.exampleBindings != null) {
				final JsonObject bindings = new JsonObject();
				b.exampleBindings.forEach(bindings::addProperty);
				o.add("example_bindings", bindings);
			}
			rows.add(o);
		}
		reply.addProperty("unsatisfied", store.unsatisfied());
		reply.addProperty("excluded", store.excluded());
		reply.add("blocked", rows);
		reply.addProperty("note",
				"a guard row counts how often the subexpression evaluated false while TLC generated the action's successors, "
						+ "attributed to the first false conjunct in TLC's evaluation order. Under a disjunction each "
						+ "false disjunct is counted, even when another disjunct let the action fire. A constraint row "
						+ "counts successors the action generated that a state or action constraint then excluded");
		if (refreshed) {
			reply.addProperty("stale", true);
			reply.addProperty("stale_reason",
					"the store was refreshed incrementally, and guards are not tallied during a replay; reopen for a fresh profile");
		}
		return reply;
	}

	void shutdown() {
		if (simulator != null && simulatorThread != null && simulatorThread.isAlive()) {
			simulator.stop();
			try {
				simulatorThread.join(5000);
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		}
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
