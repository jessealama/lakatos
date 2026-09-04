import {
  parseIssue,
  type Issue,
  type IssueKind,
} from "../engines/pabst/src/contract.js";
import type { LeanVerdict } from "../engines/thales/frontend/src/run.js";
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

/** One annotation's outcome in a lakatos run. */
export interface AnnotationResult extends PropertyIdentity {
  szs: SzsStatus;
  kind?: IssueKind | typeof UNSUPPORTED_RANGE_KIND;
  counterexample?: Record<string, unknown>;
  error?: string;
  /** Prove pipeline: the construct outside the mappable subset
   * (Inappropriate), or why the prover stopped (GaveUp, NotTried). */
  reason?: string;
  /** Theorem only: the non-standard axioms the proof depends on. Empty
   * for a kernel-checked proof. */
  axioms?: string[];
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
 * the rest ran without a counterexample and report GaveUp. A failed
 * assertion whose payload cannot be read is not a GaveUp — the run is
 * returned unreadable and the caller contains it.
 */
export function joinRefuteVerdicts(
  identities: PropertyIdentity[],
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
  const annotations = identities.map((id) => {
    const issue = flagged.get(identityKey(id));
    if (!issue) return { ...id, szs: "GaveUp" as const };
    const result: AnnotationResult = {
      ...id,
      szs: szsForIssue(issue.kind),
      kind: issue.kind,
    };
    if (issue.counterexample !== undefined)
      result.counterexample = issue.counterexample;
    if (issue.error !== undefined) result.error = issue.error;
    return result;
  });
  return { kind: "joined", annotations };
}

/** Every annotation an interrupted run never finished evaluating, in
 * envelope form: processing stopped at the user's request, and the
 * reason names the signal that asked. Annotations already resolved
 * before the engine ran keep the status they earned. */
export function interruptedResults(
  identities: PropertyIdentity[],
  signal: string,
): AnnotationResult[] {
  return identities.map((id) => ({
    ...id,
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
  identities: PropertyIdentity[],
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

export type ProveJoin =
  | { kind: "joined"; annotations: AnnotationResult[] }
  | { kind: "mismatched"; messages: string[] };

/** The Theorem reason (a run-internal kernel name) is dropped — what the
 * proof rests on travels as its axioms — and so is the CounterSatisfiable
 * one: its substance is the counterexample, which ships in the same
 * falsified shape the refutation engine uses. Error diagnostics travel in
 * `error` like every other engine failure. */
function verdictResult(
  id: PropertyIdentity,
  v: ProveVerdict,
): AnnotationResult {
  const szs = v.szs;
  if (szs === "Theorem") return { ...id, szs, axioms: v.axioms ?? [] };
  if (szs === "CounterSatisfiable")
    return { ...id, szs, kind: "falsified", counterexample: v.counterexample };
  if (szs === "Error") return { ...id, szs, error: v.reason };
  return { ...id, szs, reason: v.reason };
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
): ProveJoin {
  const messages: string[] = [];
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
    annotations.push(verdictResult(id, v));
  }
  for (const key of byKey.keys()) {
    messages.push(`verdict for unknown annotation ${key}`);
  }
  if (messages.length > 0) return { kind: "mismatched", messages };
  return { kind: "joined", annotations };
}
