import {
  parseIssue,
  type Issue,
  type IssueKind,
} from "../engines/pabst/src/contract.js";
import type { VitestJson } from "../engines/pabst/src/vitest-json.js";
import { szsForIssue, type SzsStatus } from "./szs.js";

/** Identity of one scraped annotation: where it lives and what it claims. */
export interface PropertyIdentity {
  file: string;
  function: string;
  property: string;
}

/** One annotation's outcome in a lakatos run. */
export interface AnnotationResult extends PropertyIdentity {
  szs: SzsStatus;
  kind?: IssueKind;
  counterexample?: Record<string, unknown>;
  error?: string;
  /** Inappropriate only: the construct outside the mappable subset. */
  reason?: string;
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

/** Parse every failed assertion's tagged payload into an Issue. */
export function collectIssues(json: VitestJson): Issue[] {
  const issues: Issue[] = [];
  for (const file of json.testResults ?? []) {
    for (const a of file.assertionResults ?? []) {
      if (a.status !== "failed") continue;
      const issue = parseIssue(a.failureMessages[0] ?? "");
      if (issue) issues.push(issue);
    }
  }
  return issues;
}

/**
 * Join the generated properties against the run's parsed issues: every
 * identity gets an entry — flagged ones carry the issue's kind and detail,
 * the rest ran without a counterexample and report GaveUp.
 */
export function buildEnvelope(
  meta: RunMeta,
  json: VitestJson,
  identities: PropertyIdentity[],
): Envelope {
  const flagged = new Map(
    collectIssues(json).map((i) => [
      identityKey({ file: i.file, function: i.function, property: i.property }),
      i,
    ]),
  );
  const annotations: AnnotationResult[] = identities.map((id) => {
    const issue = flagged.get(identityKey(id));
    if (!issue) return { ...id, szs: "GaveUp" };
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
  return {
    version: meta.version,
    startedAt: meta.startedAt,
    cwd: meta.cwd,
    seed: meta.seed,
    generated: meta.generated,
    passed: json.numPassedTests,
    failed: json.numFailedTests,
    annotations,
  };
}

/** Envelope for commands that scrape but do not attempt anything yet. */
export function notTriedEnvelope(
  version: string,
  startedAt: string,
  cwd: string,
  identities: PropertyIdentity[],
): Envelope {
  return {
    version,
    startedAt,
    cwd,
    annotations: identities.map((i) => ({ ...i, szs: "NotTried" })),
  };
}
