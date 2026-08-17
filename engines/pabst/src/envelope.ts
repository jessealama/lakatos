import { parseIssue, type Issue } from "./contract.js";
import type { VitestJson } from "./vitest-json.js";

/** The full report of one pabst run: metadata, counts, and parsed issues. */
export interface Envelope {
  version: string;
  startedAt: string;
  cwd: string;
  seed: number;
  generated: number;
  passed: number;
  failed: number;
  issues: Issue[];
}

export type { AssertionResult, FileResult, VitestJson } from "./vitest-json.js";

/** Run-level metadata the CLI captures, independent of the vitest run. */
export interface RunMeta {
  version: string;
  startedAt: string;
  cwd: string;
  seed: number;
  generated: number;
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

/** Assemble the full run envelope from metadata and a parsed vitest run. */
export function buildEnvelope(meta: RunMeta, json: VitestJson): Envelope {
  return {
    version: meta.version,
    startedAt: meta.startedAt,
    cwd: meta.cwd,
    seed: meta.seed,
    generated: meta.generated,
    passed: json.numPassedTests,
    failed: json.numFailedTests,
    issues: collectIssues(json),
  };
}
