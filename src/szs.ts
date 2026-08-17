import type { IssueKind } from "../engines/pabst/src/contract.js";

/**
 * SZS statuses lakatos emits (https://tptp.org/UserDocs/SZSOntology/).
 * A pass also maps to GaveUp: N clean runs refute nothing, and the engine
 * stopped of its own accord — the `kind` field disambiguates.
 */
export type SzsStatus = "CounterSatisfiable" | "GaveUp" | "Error" | "NotTried";

/** Status for a property the refutation engine flagged. */
export function szsForIssue(kind: IssueKind): SzsStatus {
  switch (kind) {
    case "falsified":
      return "CounterSatisfiable";
    case "threw":
      return "Error";
    case "exhausted":
      return "GaveUp";
  }
}
