/**
 * Lemma's public surface: the names the CLI and the engines may use.
 *
 * Everything else under `lemma/src/` is internal — exported only so one lemma
 * module can call another, so a lemma test can reach it, or so `.d.ts` emit can
 * name a type in an exported signature. Consumers outside `lemma/` import this
 * module and nothing else; `tests/lemma-surface.test.ts` enforces that.
 */

export { LemmaError } from "./errors.js";

export type {
  Binder,
  ClassCtorDomain,
  ClassDomain,
  CtorParam,
  CtorParamDomain,
  GenerablePrimitive,
  Primitive,
  Range,
  StringPattern,
} from "./binder.js";
export { isClassCtorDomain } from "./binder.js";

export { collectAtoms } from "./formula-ast.js";
export type { Formula } from "./formula-ast.js";

export { QUALIFIED_NAME_PATTERN, qualifiedName } from "./qualified-name.js";

export { mirrorPath } from "./mirror.js";

export { resolveFiles } from "./discover.js";
export type { Discovery } from "./discover.js";

export { REQUIRED_OPTIONS, typecheckProject } from "./typecheck.js";
export type { TypecheckDiagnostic, TypecheckResult } from "./typecheck.js";

export { extract, extractFromSource } from "./extract.js";
export type {
  ExtractResult,
  InvalidAnnotation,
  RawAnnotation,
} from "./extract.js";

export { parsePrefix } from "./prefix-parser.js";
export type { ParsedPrefix } from "./prefix-parser.js";

export { resolveClassBinders } from "./class-domain.js";
export type { ClassInfo, ClassTable } from "./class-domain.js";

export { parseBody } from "./formula-parser.js";

export {
  bigintBounds,
  clampedEndpoints,
  intBounds,
  intInterval,
  isClassDomain,
  isPrimitive,
  numberConstraints,
  numberDoubleConstraints,
  SAFE_INTEGER_RANGE,
  unsupportedRangeReason,
} from "./domains.js";
export type {
  IntBounds,
  IntInterval,
  NumberBound,
  NumberConstraints,
} from "./domains.js";

export { EmptyAfterClampError, parseRange } from "./range.js";

export { anchoredSource, regexGuardDomainError } from "./regex-guard.js";
