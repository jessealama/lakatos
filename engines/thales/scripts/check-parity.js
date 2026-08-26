#!/usr/bin/env node
// The envelope-diff parity harness (#146): run the old transcriber
// pipeline and the new plain-Lean emission pipeline over the fixture
// manifest, project both to per-annotation envelope entries, and require
// them identical. Both sides share one projection, so a diff here is a
// pipeline divergence, never a harness artifact. Breadth slices extend
// the manifest; without LAKATOS_PROVE_E2E=1 only the quick fixtures run,
// the same gate the prove e2e uses.

import { spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { checker, engineRoot, frontend, repoRoot } from "./harness.js";

const { transcribe } = await frontend("transcribe");
const { emitModule } = await frontend("emission");
const { parseVerdicts, runArtifact } = await frontend("run");
const { qualifiedName } = await import(
  path.join(repoRoot, "dist", "lemma", "src", "index.js")
);

const CONFORMANCE = "engines/thales/tests/conformance";

/** Always checked: the tracer bullet and the frontend-classified twin of
 * the old pipeline's class-binder refusal. */
const QUICK_FIXTURES = [
  "engines/thales/tests/fixtures/tracer.ts",
  `${CONFORMANCE}/inappropriate/class-binder.ts`,
];

/** The expression slice of the conformance corpus (#147): single-return
 * bodies, int/nat binders, single-atom conclusions. Fixtures with imports
 * or unsupported ranges join the manifest with their slices (#149, #151). */
const EXPRESSION_FIXTURES = [
  "engines/thales/tests/fixtures/operators.ts",
  `${CONFORMANCE}/theorem/add-commutes.ts`,
  `${CONFORMANCE}/theorem/bounded-double.ts`,
  `${CONFORMANCE}/theorem/endpoints.ts`,
  `${CONFORMANCE}/theorem/halve-double.ts`,
  `${CONFORMANCE}/theorem/mul-associates.ts`,
  `${CONFORMANCE}/theorem/nat-double.ts`,
  `${CONFORMANCE}/theorem/nat-open-below.ts`,
  `${CONFORMANCE}/theorem/negate-involution.ts`,
  `${CONFORMANCE}/theorem/remainder.ts`,
  `${CONFORMANCE}/theorem/succ-monotone.ts`,
  `${CONFORMANCE}/theorem/twice-parity.ts`,
  `${CONFORMANCE}/theorem/unbounded-mul-commutes.ts`,
  `${CONFORMANCE}/countersatisfiable/commutes.ts`,
  `${CONFORMANCE}/countersatisfiable/off-by-one.ts`,
  `${CONFORMANCE}/countersatisfiable/zero-edge.ts`,
  `${CONFORMANCE}/gaveup/float-assoc.ts`,
  `${CONFORMANCE}/gaveup/nonneg-int-range.ts`,
  `${CONFORMANCE}/gaveup/unbounded-double.ts`,
  `${CONFORMANCE}/gaveup/unbounded-false.ts`,
  `${CONFORMANCE}/gaveup/unbounded-nat.ts`,
  `${CONFORMANCE}/inappropriate/await-remote.ts`,
  `${CONFORMANCE}/inappropriate/class-method.ts`,
  `${CONFORMANCE}/inappropriate/exponentiation.ts`,
  `${CONFORMANCE}/error/unmodeled-operator.ts`,
  `${CONFORMANCE}/timeout/big-domain.ts`,
];

/** The statement slice (#148): statement-bodied fixtures — const and
 * mutable locals, reassignment, branches whose arms return, throw, or
 * fall through — plus the statement-level degradations (loops, a
 * shadowing redeclaration, an uninitialized let). */
const STATEMENT_FIXTURES = [
  "engines/thales/tests/fixtures/statements.ts",
  `${CONFORMANCE}/theorem/branch-joined-let.ts`,
  `${CONFORMANCE}/theorem/const-chain.ts`,
  `${CONFORMANCE}/theorem/let-binding.ts`,
  `${CONFORMANCE}/countersatisfiable/branch-throw.ts`,
  `${CONFORMANCE}/inappropriate/branch-loop.ts`,
  `${CONFORMANCE}/inappropriate/for-loop.ts`,
  `${CONFORMANCE}/inappropriate/shadowed-const.ts`,
  `${CONFORMANCE}/inappropriate/uninitialized-let.ts`,
];

/** The binder/guard slice (#150): guard chains, guard-respecting
 * witnesses, and number binders — bounded, half-bounded, and rangeless.
 * With this slice the manifest covers every shape the emission pipeline
 * reaches; imports (#149) and unsupported ranges (#151) are what still
 * wait. */
const BINDER_FIXTURES = [
  "engines/thales/tests/fixtures/binders.ts",
  `${CONFORMANCE}/countersatisfiable/guarded-witness.ts`,
  `${CONFORMANCE}/countersatisfiable/reserved-binder.ts`,
  `${CONFORMANCE}/theorem/guarded-floor.ts`,
  `${CONFORMANCE}/theorem/branch-guarded-throw.ts`,
  `${CONFORMANCE}/theorem/number-binder.ts`,
  `${CONFORMANCE}/theorem/branch-clamp.ts`,
  `${CONFORMANCE}/theorem/finite-bounds.ts`,
  `${CONFORMANCE}/theorem/left-factor.ts`,
  `${CONFORMANCE}/theorem/literal-factor.ts`,
  `${CONFORMANCE}/theorem/guarded-monotone-conversion.ts`,
  `${CONFORMANCE}/inappropriate/guarded-power.ts`,
];

/** The degradation slice (#151): unsupported ranges and the names
 * non-function declarations bind, mixed with healthy annotations in one
 * file. Imports stay out until their slice restores them. */
const DEGRADATION_FIXTURES = [
  "engines/thales/tests/fixtures/degradations.ts",
  `${CONFORMANCE}/nottried/empty-after-clamp.ts`,
  `${CONFORMANCE}/nottried/half-bounded-int.ts`,
  `${CONFORMANCE}/nottried/huge-range.ts`,
];

const fixtures =
  process.env.LAKATOS_PROVE_E2E === "1"
    ? [
        ...QUICK_FIXTURES,
        ...EXPRESSION_FIXTURES,
        ...STATEMENT_FIXTURES,
        ...BINDER_FIXTURES,
        ...DEGRADATION_FIXTURES,
      ]
    : QUICK_FIXTURES;

const { check, done } = checker("parity");

process.chdir(repoRoot); // the fixture path is the annotations' identity file
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "thales-parity-"));

// One lake build settles the emitter; each fixture then pays only the
// process spawn, with lake's search path captured once.
const emitBin = path.join(engineRoot, ".lake", "build", "bin", "thales-emit");
const emitBuild = spawnSync("lake", ["build", "thales-emit"], {
  cwd: engineRoot,
  encoding: "utf8",
  timeout: 600_000,
});
check(
  emitBuild.status === 0,
  `lake build thales-emit failed (${emitBuild.status}):\n${emitBuild.stderr}`,
);
const leanPath = spawnSync("lake", ["env", "printenv", "LEAN_PATH"], {
  cwd: engineRoot,
  encoding: "utf8",
  timeout: 600_000,
}).stdout?.trim();
check(Boolean(leanPath), "lake env yielded no LEAN_PATH");

/** One envelope entry, as both pipelines must produce it. `kind` rides
 * only on the refusals that carry one into the envelope. */
function entry(fn, property, szs, reason, axioms, counterexample, kind) {
  return { function: fn, property, szs, reason, axioms, counterexample, kind };
}

/** A native_decide axiom's ordinal is a per-file gensym — it counts the
 * elaborator's attempts, not anything about the annotation — so the
 * comparison masks it; the axiom's identity is the rest of the name. */
function maskAxiom(name) {
  return name.replace(/native_decide\.ax_\d+$/, "native_decide.ax_N");
}

function projectVerdict(v) {
  return entry(
    v.identity[1],
    v.identity[2],
    v.szs,
    v.reason,
    v.axioms?.map(maskAxiom),
    v.counterexample,
  );
}

/** An annotation the old transcriber deliberately emitted no command for,
 * as the CLI reports it from the untried kind. */
function projectUntried(u) {
  const fn = qualifiedName(
    u.annotation.functionName,
    u.annotation.className,
    u.annotation.isStatic,
  );
  const szs = u.kind === "class-binder" ? "Inappropriate" : "NotTried";
  // The CLI carries the kind into the envelope only for NotTried refusals.
  const kind = u.kind === "class-binder" ? undefined : u.kind;
  return entry(
    fn,
    u.annotation.propertyName,
    szs,
    u.reason,
    undefined,
    undefined,
    kind,
  );
}

const identityOf = (a) =>
  `${qualifiedName(a.functionName, a.className, a.isStatic)} ${a.propertyName}`;

/** Run one artifact and return its verdicts, failing the check run on any
 * channel violation. */
function verdictsOf(leanFile, label) {
  const run = runArtifact(engineRoot, leanFile);
  check(run.error === undefined, `${label}: failed to run lake: ${run.error}`);
  check(
    run.status === 0,
    `${label}: expected exit 0, got ${run.status}\nstderr:\n${run.stderr}`,
  );
  const { verdicts, messages } = parseVerdicts(run.stdout ?? "");
  for (const m of messages) check(false, `${label}: ${m}`);
  return verdicts;
}

for (const [i, fixture] of fixtures.entries()) {
  const text = fs.readFileSync(fixture, "utf8");

  // Timeout fixtures are graded the way the corpus harness grades them:
  // under a reduced heartbeat budget, where Timeout is deterministic and
  // cheap. Both pipelines see the same budget, so parity still binds.
  if (fixture.includes("/timeout/")) {
    process.env.LAKATOS_PROVE_HEARTBEATS = "1";
  } else {
    delete process.env.LAKATOS_PROVE_HEARTBEATS;
  }

  // Old pipeline: transcribe, run, one verdict line per annotation that
  // got a command; untried annotations are reported the way the CLI does.
  const oldSide = (() => {
    const { lean, annotations, untried } = transcribe(text, fixture);
    const leanFile = path.join(tmp, `old-${i}.lean`);
    fs.writeFileSync(leanFile, lean);
    const byIdentity = new Map(
      verdictsOf(leanFile, `${fixture}: old pipeline`).map((v) => [
        `${v.identity[1]} ${v.identity[2]}`,
        projectVerdict(v),
      ]),
    );
    for (const u of untried) {
      byIdentity.set(identityOf(u.annotation), projectUntried(u));
    }
    return {
      annotations,
      entries: annotations.map((a) => byIdentity.get(identityOf(a))),
    };
  })();

  // New pipeline: emit JSON, render with thales-emit, run the artifact,
  // and join the Lean verdicts with the frontend's own classifications in
  // annotation order.
  const newSide = (() => {
    const { emission, annotations, classified } = emitModule(text, fixture);
    const jsonFile = path.join(tmp, `emission-${i}.json`);
    const leanFile = path.join(tmp, `new-${i}.lean`);
    fs.writeFileSync(jsonFile, JSON.stringify(emission));
    const emit = spawnSync(emitBin, [jsonFile, leanFile], {
      cwd: engineRoot,
      encoding: "utf8",
      timeout: 120_000,
      env: { ...process.env, LEAN_PATH: leanPath },
    });
    check(
      emit.status === 0,
      `${fixture}: thales-emit failed (${emit.status}):\n${emit.stderr}`,
    );
    if (emit.status !== 0) return { annotations, entries: [] };
    const byIdentity = new Map(
      verdictsOf(leanFile, `${fixture}: new pipeline`).map((v) => [
        `${v.identity[1]} ${v.identity[2]}`,
        projectVerdict(v),
      ]),
    );
    for (const c of classified) {
      const fn = qualifiedName(
        c.annotation.functionName,
        c.annotation.className,
        c.annotation.isStatic,
      );
      byIdentity.set(
        `${fn} ${c.annotation.propertyName}`,
        entry(
          fn,
          c.annotation.propertyName,
          c.szs,
          c.reason,
          undefined,
          undefined,
          c.kind,
        ),
      );
    }
    return {
      annotations,
      entries: annotations.map((a) => byIdentity.get(identityOf(a))),
    };
  })();

  check(
    oldSide.annotations.length === newSide.annotations.length,
    `${fixture}: the two pipelines extracted different annotation sets`,
  );
  check(
    oldSide.entries.every((e) => e !== undefined) &&
      newSide.entries.every((e) => e !== undefined),
    `${fixture}: a pipeline left annotations unaccounted for\nold:\n${JSON.stringify(oldSide.entries, null, 2)}\nnew:\n${JSON.stringify(newSide.entries, null, 2)}`,
  );
  check(
    JSON.stringify(oldSide.entries) === JSON.stringify(newSide.entries),
    `${fixture}: envelope entries diverge\nold:\n${JSON.stringify(oldSide.entries, null, 2)}\nnew:\n${JSON.stringify(newSide.entries, null, 2)}`,
  );
}

fs.rmSync(tmp, { recursive: true, force: true });

done(`${fixtures.length} fixtures, both pipelines`);
