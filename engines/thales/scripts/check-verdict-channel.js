#!/usr/bin/env node
// Checks the JSON verdict-line contract between ThalesDsl's #thales_prove
// command elaborator and the CLI: one parseable line per command on stdout,
// in command order, failures contained per command, clean exit. The channel
// itself — the sentinel, the parse, the verdict validation, the lake
// invocation and its timeout — comes from the built frontend, so this
// checks production's reader rather than a second copy of it.

import * as path from "node:path";
import { checker, engineRoot, frontend } from "./harness.js";

const { parseVerdicts, runArtifact } = await frontend("run");

// Expected [function, szs, reasonPattern?, counterexample?] sequence per
// fixture, in command order; reasonPattern, when present, must match the
// reason; counterexample, when present, must deep-equal the verdict's
// (and only expected entries may carry one).
const FIXTURES = [
  {
    file: "verdict-channel.lean",
    expected: [
      ["add", "NotTried"],
      ["sub", "NotTried"],
      ["bad", "Error", /^property elaboration failed/],
      ["tail", "NotTried"],
    ],
  },
  {
    // The plain-Prop payload the emission pipeline writes, structured and
    // bare forms alike.
    file: "theorem-plain.lean",
    expected: [
      [
        "add",
        "Theorem",
        /proved by a decision procedure over the bounded domain, kernel-checked as/,
      ],
      ["double", "CounterSatisfiable", /false on its bounded domain/, { a: 1 }],
      ["dbl", "NotTried"],
    ],
  },
  {
    // Binder heads the emission pipeline writes: each row is the verdict
    // the ladder gives that binder shape.
    file: "binder-shapes-plain.lean",
    expected: [
      ["ident", "CounterSatisfiable", /false on its bounded domain/, { x: -3 }],
      ["ident", "GaveUp", /unsolved goal:[\s\S]*Float\.ofInt x = 0/],
      ["ident", "GaveUp", /unsolved goal:[\s\S]*0 ≤ n →/],
      // A ranged binder over an unbounded one: both survive into the goal.
      ["ident", "GaveUp", /unsolved goal:[\s\S]*x < 3 → ∀ \(n : Int\)/],
    ],
  },
  {
    // Guard chains in the plain-Prop payload.
    file: "guard-chain-plain.lean",
    expected: [
      ["idg", "Theorem", /decision procedure over the bounded domain/],
      ["idg", "Theorem", /decision procedure over the bounded domain/],
      // A constant-false guard: vacuous truth, still a Theorem.
      ["idg", "Theorem", /decision procedure over the bounded domain/],
      // A guard under a number binder reaches the symbolic rungs, which
      // close the identity case from the guard hypothesis.
      ["idg", "Theorem", /generic proof search/],
      // The witness respects the guard: never x = 0.
      ["idg", "CounterSatisfiable", /false/, { x: 5 }],
    ],
  },
  {
    file: "theorem-arith.lean",
    expected: [
      ...Array.from({ length: 7 }, () => [
        "add",
        "Theorem",
        /proved by a decision procedure over the bounded domain, kernel-checked as/,
      ]),
      // Integer binder values coerced into a binary64 body: narrow enough
      // for the kernel to enumerate, then wide enough that only evaluation
      // can. The trust wording is read off each proof's axioms.
      [
        "dbl",
        "Theorem",
        /proved by a decision procedure over the bounded domain, kernel-checked as/,
      ],
      [
        "dbl",
        "Theorem",
        /trusted from evaluation rather than checked by the kernel/,
      ],
      [
        "add",
        "Theorem",
        /proved by a decision procedure over the bounded domain, kernel-checked as/,
      ],
    ],
  },
  {
    file: "countersatisfiable.lean",
    expected: [
      ["bump", "CounterSatisfiable", /false/, { x: 0 }],
      ["sq", "CounterSatisfiable", /false/, { x: 0 }],
      ["comm", "CounterSatisfiable", /false/, { a: 0, b: 1 }],
      ["bump", "GaveUp", /^the property is false on its bounded domain$/],
      // Falsity outlives the witness search that ran out of budget: the
      // counterexample is gone, the verdict is not, and it is not a Timeout.
      ["bump", "GaveUp", /^the property is false on its bounded domain$/],
    ],
  },
  // The symbolic rungs have no binary64 theory to work with yet, so an
  // unbounded binder leaves a residual goal rather than a proof. The
  // residual is the point: it names the fact the theory worklist needs.
  {
    file: "gaveup-generic.lean",
    expected: [
      ["dbl", "GaveUp", /unsolved goal:[\s\S]*Float\.ofInt/],
      ["dbl", "GaveUp", /unsolved goal:[\s\S]*Float\.ofInt/],
      ["dbl", "GaveUp", /unsolved goal:[\s\S]*Float\.ofInt/],
    ],
  },
  {
    file: "gaveup-grind.lean",
    expected: [["mul", "GaveUp", /unsolved goal:[\s\S]*Float\.ofInt/]],
  },
  {
    file: "gaveup-goal.lean",
    expected: [
      ["bump", "GaveUp", /unsolved goal:[\s\S]*\+ 1 = /],
      // Bounded, but past the evaluation cap: no tier can settle it inside
      // the annotation's budget, so the attempt reports as budget-bound.
      ["wide", "Timeout", /heartbeat budget/],
    ],
  },
  {
    file: "recdepth.lean",
    expected: [
      ["bump", "GaveUp", /^unsolved goal:[\s\S]*bump/],
      ["bump", "Error", /^property elaboration failed/],
      ["bump", "Theorem"],
    ],
  },
  {
    file: "timeout.lean",
    expected: [
      ["slow", "Timeout", /heartbeat budget/],
      ["add", "Theorem"],
      ["slow", "Timeout", /heartbeat budget/],
      ["slow", "Timeout", /thales\.heartbeats = 1\)$/],
    ],
  },
  {
    // Five guards, one of them on a field the property never reads: a
    // guard the goal never reaches leaves no trace to prove twice.
    file: "class-binder-wide.lean",
    expected: [["Wide#distance", "Theorem"]],
  },
  {
    // Seven guards over two binders, the shape a split of the image could
    // not reach: the facts are linear in the guards, so it proves at the
    // default budget like the narrower ones.
    file: "class-binder-wider.lean",
    expected: [["Wide#distance", "Theorem"]],
  },
  {
    // A symbolic rung's starvation. The obligation is provable — the
    // default budget closes it — so a reduced budget must report as
    // budget-bound rather than as a residual goal nobody can move.
    file: "timeout-symbolic.lean",
    expected: [["Wide#distance", "Timeout", /heartbeat budget/]],
  },
  {
    // The grind rung's starvation: enough budget for the generic rung to
    // normalize and hand over a residual, not enough for grind to close
    // it. Grind converts its own exhaustion into a plain failure, so the
    // ladder has to read the spent budget back out of the result.
    file: "timeout-grind.lean",
    expected: [["Wide#distance", "Timeout", /thales\.heartbeats = 8000\)$/]],
  },
  {
    file: "theorem-rescue.lean",
    expected: [["dbl", "Theorem"]],
  },
  {
    // The class shapes: a structure, its single-assignment constructor in
    // both the plain-let and let-mut forms, a getter, and an
    // instance-taking method. Every round-trip is kernel-checked, the
    // guarded one through the refuted throw arm.
    file: "class-core-plain.lean",
    expected: [
      ["Box#v", "Theorem", /generic proof search, kernel-checked as/],
      ["Box#double", "Theorem", /generic proof search, kernel-checked as/],
      ["Gate#lo", "Theorem", /generic proof search, kernel-checked as/],
    ],
  },
  {
    // A class-valued binder: the instance ranges over the constructor's
    // image, so the ladder has to invert that hypothesis before any closer
    // sees the fields. Kernel-checked, on the guarding constructor.
    file: "class-binder-plain.lean",
    expected: [
      ["Point#distance", "Theorem", /generic proof search, kernel-checked as/],
    ],
  },
  {
    // Five guards, two of them clamps. The arms a normalization already
    // settled prune before the closers run, which is what keeps this at
    // the default budget.
    file: "class-binder-clamp.lean",
    expected: [["Clamp#distance", "Theorem"]],
  },
];

const { check, done } = checker("verdict-channel");

for (const { file, expected } of FIXTURES) {
  const run = runArtifact(
    engineRoot,
    path.join(engineRoot, "tests", "fixtures", file),
  );

  check(run.error === undefined, `${file}: failed to run lake: ${run.error}`);
  check(
    run.status === 0,
    `${file}: expected exit 0, got ${run.status}\nstderr:\n${run.stderr}`,
  );

  const { verdicts, diagnostics, messages } = parseVerdicts(run.stdout ?? "");
  check(
    diagnostics.length === 0,
    `${file}: unframed stdout line(s):\n${diagnostics.join("\n")}`,
  );
  for (const m of messages) check(false, `${file}: ${m}`);
  check(
    verdicts.length === expected.length,
    `${file}: expected ${expected.length} verdict lines, got ${verdicts.length}:\n${run.stdout}`,
  );

  if (verdicts.length === expected.length) {
    const got = verdicts.map((v) => [v.identity[1], v.szs]);
    const want = expected.map(([fn, szs]) => [fn, szs]);
    check(
      JSON.stringify(got) === JSON.stringify(want),
      `${file}: expected verdicts ${JSON.stringify(want)}, got ${JSON.stringify(got)}`,
    );
    for (const [i, [, , reasonPattern, counterexample]] of expected.entries()) {
      if (reasonPattern !== undefined) {
        check(
          reasonPattern.test(verdicts[i].reason),
          `${file}: verdict ${i} reason ${JSON.stringify(verdicts[i].reason)} does not match ${reasonPattern}`,
        );
      }
      check(
        JSON.stringify(verdicts[i].counterexample) ===
          JSON.stringify(counterexample),
        `${file}: verdict ${i} counterexample ${JSON.stringify(verdicts[i].counterexample)}, expected ${JSON.stringify(counterexample)}`,
      );
    }
  }

  // Every Theorem names what it rests on, and the list must agree with the
  // trust wording: a kernel-checked proof uses no extra axioms, an
  // evaluation-trusted one exactly the native-evaluation axiom under its
  // canonical spelling. Nothing but a Theorem carries the field.
  for (const [i, v] of verdicts.entries()) {
    if (v.szs !== "Theorem") {
      check(
        v.axioms === undefined,
        `${file}: verdict ${i} (${v.szs}) carries axioms ${JSON.stringify(v.axioms)}`,
      );
      continue;
    }
    check(
      Array.isArray(v.axioms),
      `${file}: Theorem verdict ${i} carries no axioms array`,
    );
    if (/kernel-checked/.test(v.reason)) {
      check(
        v.axioms.length === 0,
        `${file}: kernel-checked verdict ${i} carries axioms ${JSON.stringify(v.axioms)}`,
      );
    } else {
      check(
        JSON.stringify(v.axioms) === JSON.stringify(["Lean.ofReduceBool"]),
        `${file}: evaluation-trusted verdict ${i} axioms ${JSON.stringify(v.axioms)} are not exactly the native-evaluation axiom`,
      );
    }
  }
}

done(`${FIXTURES.length} fixtures`);
