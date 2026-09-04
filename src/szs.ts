import type { IssueKind } from "../engines/pabst/src/contract.js";

/**
 * SZS statuses lakatos emits (https://tptp.org/UserDocs/SZSOntology/), the
 * single source of truth for the vocabulary: the union, the prove subset,
 * and the engine-side allowlist all derive from this array.
 * A pass also maps to GaveUp when the domain was sampled: N clean runs
 * refute nothing, and the engine stopped of its own accord — the `kind`
 * field disambiguates. A pass over a domain the refuter walked in full is
 * a Theorem, `kind` enumerated. Theorem and
 * Inappropriate come from the prove pipeline: a property proven for all
 * inputs, and an annotation depending on code outside the mappable subset
 * (its `reason` names the offending construct). CounterSatisfiable comes
 * from either engine — a sampled counterexample from refute, or a witness
 * searched out of a bounded domain that decide established false — in the
 * same falsified shape either way. InputError marks an
 * annotation whose input is malformed at extraction (a duplicate property
 * name, an inaccessible subject) or whose program fails to type check;
 * its `error` carries the diagnostic and the run exits 2, the documented
 * error mode. Timeout marks an annotation whose proof attempt exceeded
 * its per-annotation budget, or whose enumeration ran out of wall clock
 * before walking its domain; later annotations in the same file still
 * run. User marks an annotation an interrupted run never finished
 * evaluating: processing stopped at the user's request.
 */
export const SZS_STATUSES = [
  "Theorem",
  "CounterSatisfiable",
  "GaveUp",
  "Error",
  "NotTried",
  "Inappropriate",
  "InputError",
  "Timeout",
  "User",
] as const;

export type SzsStatus = (typeof SZS_STATUSES)[number];

/** Statuses the CLI synthesizes, which no prover verdict can carry:
 * extraction happens on the CLI side, and an interrupted engine reports
 * nothing at all, so the prove contract never has to represent them. */
const CLI_ONLY_STATUSES = ["InputError", "User"] as const;

type CliOnlyStatus = (typeof CLI_ONLY_STATUSES)[number];

/** The verdict statuses the prove contract carries. ThalesDsl's `Szs`
 * enumerates exactly these — tests/verdict-contract.test.ts pins the two. */
export type ProveStatus = Exclude<SzsStatus, CliOnlyStatus>;

export const PROVE_STATUSES: ReadonlySet<ProveStatus> = new Set(
  SZS_STATUSES.filter(
    (s): s is ProveStatus =>
      !(CLI_ONLY_STATUSES as readonly string[]).includes(s),
  ),
);

export function isProveStatus(s: string): s is ProveStatus {
  return (PROVE_STATUSES as ReadonlySet<string>).has(s);
}

/** Status for a property the refutation engine flagged. */
export function szsForIssue(kind: IssueKind): SzsStatus {
  switch (kind) {
    case "falsified":
      return "CounterSatisfiable";
    case "threw":
      return "Error";
    case "exhausted":
      return "GaveUp";
    case "budget":
      return "Timeout";
  }
}
