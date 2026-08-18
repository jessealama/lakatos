import type { IssueKind } from "../engines/pabst/src/contract.js";

/**
 * SZS statuses lakatos emits (https://tptp.org/UserDocs/SZSOntology/).
 * A pass also maps to GaveUp: N clean runs refute nothing, and the engine
 * stopped of its own accord — the `kind` field disambiguates. Theorem and
 * Inappropriate come from the prove pipeline: a property proven for all
 * inputs, and an annotation depending on code outside the mappable subset
 * (its `reason` names the offending construct). InputError marks an
 * annotation whose input is malformed at extraction (a duplicate property
 * name, an inaccessible subject); its `error` carries the diagnostic and
 * the run exits via the unhealthy path.
 */
export type SzsStatus =
  | "Theorem"
  | "CounterSatisfiable"
  | "GaveUp"
  | "Error"
  | "NotTried"
  | "Inappropriate"
  | "InputError";

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
