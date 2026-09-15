import {
  parseIssue,
  type Issue,
  type IssueKind,
} from "../engines/pabst/src/contract.js";
import type {
  LeanVerdict,
  ModelLine,
} from "../engines/thales/frontend/src/run.js";
import type { VitestJson } from "../engines/pabst/src/vitest-json.js";
import { isProveStatus, szsForIssue, type SzsStatus } from "./szs.js";

/** Identity of one scraped annotation: where it lives and what it claims. */
export interface PropertyIdentity {
  file: string;
  function: string;
  property: string;
}

/** The one kind outside pabst's Issue kinds: a NotTried whose range only
 * fits the prover's domain after the safe-integer clamp. The schema's
 * branch is pinned to this spelling by test; thales's own literal is
 * pinned by the type union. */
export const UNSUPPORTED_RANGE_KIND = "unsupported-range" as const;

/** D8's field: what the prover established about its model of the
 * annotated declaration. Nested under its own key so `reason` never
 * collides with the verdict's own, and `reason` is present exactly when
 * the model is unvalidated. */
export type ModelField =
  { status: "validated" } | { status: "unvalidated"; reason: string };

/** The statuses that carry the model field. A prover's Theorem must have
 * one; the other four carry it when the prover reached them. Every other
 * status — the prover's Error and NotTried, and every refuter result —
 * leaves it off, and the envelope schema makes it a violation there. */
export const MODEL_CARRIERS: ReadonlySet<SzsStatus> = new Set<SzsStatus>([
  "Theorem",
  "GaveUp",
  "Timeout",
  "CounterSatisfiable",
  "Inappropriate",
]);

/** The reason a declaration the artifact printed no model line for
 * carries: a class member (until the emitter states their obligations),
 * or an emitter that forgot one. Nothing was proved either way, so the
 * model is unvalidated and says so. */
export function unstatedModelReason(fn: string): string {
  return `no correspondence obligation was stated for '${fn}'`;
}

/** The model field one annotation gets: undefined for a status that does
 * not carry it, the line's own account where there is a line, and the
 * unstated reason where there is none. One function, so the CLI join and
 * the envelope store read the field off the same rule. */
export function modelFor(
  szs: SzsStatus,
  line: ModelLine | undefined,
  fn: string,
): ModelField | undefined {
  if (!MODEL_CARRIERS.has(szs)) return undefined;
  if (line === undefined)
    return { status: "unvalidated", reason: unstatedModelReason(fn) };
  return line.status === "validated"
    ? { status: "validated" }
    : { status: "unvalidated", reason: line.reason };
}

/** One annotation's outcome in a lakatos run. Beyond the refutation
 * kinds, `unsupported-range` marks a NotTried whose range only fits the
 * prover's domain after the safe-integer clamp, and `enumerated` a
 * Theorem the refuter earned by walking the whole domain. */
export interface AnnotationResult extends PropertyIdentity {
  szs: SzsStatus;
  kind?: IssueKind | typeof UNSUPPORTED_RANGE_KIND | "enumerated";
  counterexample?: Record<string, unknown>;
  error?: string;
  /** Prove pipeline: the construct outside the mappable subset
   * (Inappropriate), or why the prover stopped (GaveUp, NotTried).
   * Refute pipeline: how far a budget-expired enumeration got (Timeout). */
  reason?: string;
  /** Theorem from the prover only: the non-standard axioms the proof
   * depends on. Empty for a kernel-checked proof. */
  axioms?: string[];
  /** Theorem from the refuter only: how many tuples it evaluated. */
  cases?: number;
  /** Prover annotations only (D8): whether the declaration's model was
   * proved equal to the evaluator's run of its own syntax tree, and why
   * not. Required on a proven Theorem; carried on GaveUp, Timeout,
   * CounterSatisfiable, and Inappropriate from the prover; never on a
   * refuter result, an Error, or a NotTried. */
  model?: ModelField;
}

/** What codegen planned for one annotation: its identity, plus, when the
 * refuter walks the whole domain, the tuple count the join will report. */
export interface PlannedProperty extends PropertyIdentity {
  cases?: number;
}

/** The identity alone. Planning detail must never reach the envelope by
 * spread: every result shape but the enumerated Theorem rejects it. */
export function identityOf(p: PropertyIdentity): PropertyIdentity {
  return { file: p.file, function: p.function, property: p.property };
}

/** Run metadata the refute command captures before running tests. */
export interface RunMeta {
  version: string;
  startedAt: string;
  cwd: string;
  seed: number;
  generated: number;
}

/** The full report of one lakatos run. Stub commands omit the run stats. */
export interface Envelope {
  version: string;
  startedAt: string;
  cwd: string;
  seed?: number;
  generated?: number;
  passed?: number;
  failed?: number;
  annotations: AnnotationResult[];
}

function identityKey(i: PropertyIdentity): string {
  return JSON.stringify([i.file, i.function, i.property]);
}

/** How each failed assertion reads back out of the run: a parsed payload
 * becomes an Issue; a failed assertion no message of which carries a
 * readable payload means the reporter never ran, and is returned as a
 * diagnostic line instead of a verdict. */
export interface CollectedIssues {
  issues: Issue[];
  unreadable: string[];
}

/** The payload is not always the first failure message vitest reports, so
 * each entry is searched. */
export function collectIssues(json: VitestJson): CollectedIssues {
  const issues: Issue[] = [];
  const unreadable: string[] = [];
  for (const file of json.testResults ?? []) {
    for (const a of file.assertionResults ?? []) {
      if (a.status !== "failed") continue;
      const messages = a.failureMessages ?? [];
      const issue = messages.map((m) => parseIssue(m)).find((i) => i !== null);
      if (issue) {
        issues.push(issue);
        continue;
      }
      const head = messages.find((m) => m.trim() !== "")?.split("\n", 1)[0];
      unreadable.push(
        head === undefined
          ? "a failed test carries no failure message"
          : `a failed test carries no readable issue payload: ${head}`,
      );
    }
  }
  return { issues, unreadable };
}

export type RefuteJoin =
  | { kind: "joined"; annotations: AnnotationResult[] }
  | {
      /** The engine reported a failure the join cannot read: no verdict
       * can be trusted, so none ship. */
      kind: "unreadable";
      messages: string[];
    };

/**
 * Join the generated properties against the run's parsed issues: every
 * identity gets an entry — flagged ones carry the issue's kind and detail,
 * the rest ran without a counterexample. A pass over a planned enumeration
 * is the Theorem; a pass over a sampled domain is only a GaveUp. A failed
 * assertion whose payload cannot be read is not a GaveUp — the run is
 * returned unreadable and the caller contains it.
 */
export function joinRefuteVerdicts(
  identities: PlannedProperty[],
  json: VitestJson,
): RefuteJoin {
  const { issues, unreadable } = collectIssues(json);
  if (unreadable.length > 0)
    return { kind: "unreadable", messages: unreadable };
  const flagged = new Map(
    issues.map((i) => [
      identityKey({ file: i.file, function: i.function, property: i.property }),
      i,
    ]),
  );
  const annotations = identities.map((planned) => {
    const id = identityOf(planned);
    const issue = flagged.get(identityKey(id));
    if (!issue) {
      // A pass carries no message: only the plan says whether the whole
      // domain was walked.
      if (planned.cases === undefined) return { ...id, szs: "GaveUp" as const };
      return {
        ...id,
        szs: "Theorem" as const,
        kind: "enumerated" as const,
        cases: planned.cases,
      };
    }
    const result: AnnotationResult = {
      ...id,
      szs: szsForIssue(issue.kind),
      kind: issue.kind,
    };
    if (issue.counterexample !== undefined)
      result.counterexample = issue.counterexample;
    if (issue.error !== undefined) result.error = issue.error;
    if (issue.reason !== undefined) result.reason = issue.reason;
    return result;
  });
  return { kind: "joined", annotations };
}

/** Every annotation an interrupted run never finished evaluating, in
 * envelope form: processing stopped at the user's request, and the
 * reason names the signal that asked. Annotations already resolved
 * before the engine ran keep the status they earned. */
export function interruptedResults(
  identities: PlannedProperty[],
  signal: string,
): AnnotationResult[] {
  return identities.map((p) => ({
    ...identityOf(p),
    szs: "User" as const,
    reason: `the run was interrupted (${signal})`,
  }));
}

/** The whole envelope for a completed, readable refutation run. Only tests
 * assemble envelopes this way; an unreadable run throws rather than
 * pretending to verdicts. */
export function buildEnvelope(
  meta: RunMeta,
  json: VitestJson,
  identities: PlannedProperty[],
): Envelope {
  const join = joinRefuteVerdicts(identities, json);
  if (join.kind === "unreadable") throw new Error(join.messages.join("\n"));
  return {
    version: meta.version,
    startedAt: meta.startedAt,
    cwd: meta.cwd,
    seed: meta.seed,
    generated: meta.generated,
    passed: json.numPassedTests,
    failed: json.numFailedTests,
    annotations: join.annotations,
  };
}

/** One #thales_prove verdict line; run.ts, which parses the wire
 * format, owns the shape. */
export type ProveVerdict = LeanVerdict;

/** One #thales_validate model line, the same way. */
export type ProveModelLine = ModelLine;

export type ProveJoin =
  | { kind: "joined"; annotations: AnnotationResult[] }
  | { kind: "mismatched"; messages: string[] };

/** The Theorem reason (a run-internal kernel name) is dropped — what the
 * proof rests on travels as its axioms — and so is the CounterSatisfiable
 * one: its substance is the counterexample, which ships in the same
 * falsified shape the refutation engine uses. Error diagnostics travel in
 * `error` like every other engine failure. */
function verdictResult(
  p: PropertyIdentity,
  v: ProveVerdict,
  line: ModelLine | undefined,
): AnnotationResult {
  const id = identityOf(p);
  const szs = v.szs;
  const model = modelFor(szs, line, p.function);
  // Spread only where the status carries it, so the Error and NotTried
  // shapes stay exactly as bare as the schema says they are.
  const m = model === undefined ? {} : { model };
  if (szs === "Theorem") return { ...id, szs, axioms: v.axioms ?? [], ...m };
  if (szs === "CounterSatisfiable")
    return {
      ...id,
      szs,
      kind: "falsified",
      counterexample: v.counterexample,
      ...m,
    };
  if (szs === "Error") return { ...id, szs, error: v.reason };
  return { ...id, szs, reason: v.reason, ...m };
}

/**
 * Join the extracted identities against the prover's verdict lines. The
 * emitter writes exactly one #thales_prove per annotation it does not
 * classify itself, so a missing, duplicate, or surplus verdict means the
 * run cannot be trusted.
 */
export function joinProveVerdicts(
  identities: PropertyIdentity[],
  verdicts: ProveVerdict[],
  models: ProveModelLine[],
): ProveJoin {
  const messages: string[] = [];
  // A model line is per declaration, so one line serves every annotation
  // of its function. A second line for the same declaration is a channel
  // violation, as unhealthy as a duplicate verdict; a line for a function
  // no annotation names is not — the emitter states an obligation for
  // every entry-module declaration, annotated or not.
  const modelByKey = new Map<string, ProveModelLine>();
  for (const m of models) {
    const key = JSON.stringify([m.file, m.function]);
    if (modelByKey.has(key)) messages.push(`duplicate model line for ${key}`);
    modelByKey.set(key, m);
  }
  const byKey = new Map<string, ProveVerdict>();
  for (const v of verdicts) {
    const key = identityKey({
      file: v.identity[0],
      function: v.identity[1],
      property: v.identity[2],
    });
    if (byKey.has(key)) messages.push(`duplicate verdict for ${key}`);
    if (!isProveStatus(v.szs)) {
      messages.push(
        `verdict status ${JSON.stringify(v.szs)} for ${key} is not representable in the envelope`,
      );
    }
    // An empty counterexample object counts as none: the envelope schema
    // requires at least one binder/value pair on a falsified annotation.
    if (
      v.szs === "CounterSatisfiable" &&
      (v.counterexample === undefined ||
        Object.keys(v.counterexample).length === 0)
    ) {
      messages.push(
        `CounterSatisfiable verdict for ${key} carries no counterexample`,
      );
    }
    byKey.set(key, v);
  }
  const annotations: AnnotationResult[] = [];
  for (const id of identities) {
    const key = identityKey(id);
    const v = byKey.get(key);
    if (v === undefined) {
      messages.push(`no verdict for ${key}`);
      continue;
    }
    byKey.delete(key);
    annotations.push(
      verdictResult(
        id,
        v,
        modelByKey.get(JSON.stringify([id.file, id.function])),
      ),
    );
  }
  for (const key of byKey.keys()) {
    messages.push(`verdict for unknown annotation ${key}`);
  }
  if (messages.length > 0) return { kind: "mismatched", messages };
  return { kind: "joined", annotations };
}
