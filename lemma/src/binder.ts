export type Primitive =
  "int" | "nat" | "number" | "boolean" | "string" | "bigint";

/** The ES primitives a constructor parameter may be annotated with. */
export type GenerablePrimitive = "number" | "boolean" | "string" | "bigint";

export interface CtorParam {
  name: string;
  domain: GenerablePrimitive;
}

/** A class-valued domain: the binder ranges over the image of successful
 * construction (spec/semantics.md, "Class-valued binders"). The parser
 * carries only the name; resolution against the annotated module attaches
 * the constructor parameters. */
export interface ClassDomain {
  className: string;
  ctorParams?: CtorParam[];
}

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
  domain: Primitive | ClassDomain;
  range?: Range;
  pattern?: StringPattern;
}
