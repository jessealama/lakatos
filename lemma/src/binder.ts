export type Domain = "int" | "nat" | "number" | "boolean" | "string" | "bigint";

/** Interval constraint on a numeric binder. Endpoints are the user's
 * literal text, kept verbatim so floats are emitted exactly as written —
 * except a leading `+`, redundant leading zeros, and a bigint `n` suffix
 * are stripped (lowering re-adds `n` for bigint). An absent endpoint is
 * unbounded (the user wrote -∞ / ∞); an open flag means that side's
 * endpoint is excluded. */
export interface Range {
  min?: string;
  max?: string;
  minOpen?: boolean;
  maxOpen?: boolean;
}

/** Regex guard on a string binder. Source and flags are the user's literal
 * text, kept verbatim; lowering anchors the source (see anchoredSource in
 * regex-guard.ts) so the guard means whole-string membership. */
export interface StringPattern {
  source: string;
  flags: string;
}

export interface Binder {
  varName: string;
  domain: Domain;
  range?: Range;
  pattern?: StringPattern;
}
