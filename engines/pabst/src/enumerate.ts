import {
  type Binder,
  bigintBounds,
  type ClassCtorDomain,
  type CtorParam,
  intInterval,
  isClassCtorDomain,
  isClassDomain,
  prefixCardinality,
  qualifiedName,
} from "../../../lemma/src/index.js";
import { BUDGET_ALIAS, REPORT_ALIAS } from "./contract.js";
import { ctorCall, ctorShape } from "./ctor.js";
import type { PropertySpec } from "./ir.js";

/** Largest domain the refuter walks in full instead of sampling. */
export const ENUMERATION_CAP = 1000n;

/** Wall clock an enumerated test may spend in its loop. */
export const LOOP_BUDGET_MS = 4000;

/** The per-test timeout the emitted test declares. vitest's timer cannot
 * interrupt a synchronous loop, so it must sit above the loop budget. */
export const TEST_TIMEOUT_MS = 8000;

/** The tuple count when the spec is walked in full, else undefined. */
export function enumerationCases(binders: Binder[]): number | undefined {
  const n = prefixCardinality(binders);
  return n === undefined || n > ENUMERATION_CAP ? undefined : Number(n);
}

/** The loop over one finite binder, ascending. */
export function loopHeader(binder: Binder): string {
  const { varName: v, domain, range } = binder;
  if (!isClassDomain(domain)) {
    if (domain === "boolean") return `for (const ${v} of [false, true]) {`;
    if (domain === "int" || domain === "nat") {
      const { lo, hi } = intInterval(domain, range ?? {});
      if (lo !== undefined && hi !== undefined) {
        // The loop counter is a number, so the decimal endpoints it is
        // written with only denote themselves inside the safe range.
        const safe = BigInt(Number.MAX_SAFE_INTEGER);
        if (lo < -safe || hi > safe)
          throw new Error(
            `binder '${v}' has endpoints outside the safe integer range`,
          );
        return `for (let ${v} = ${lo}; ${v} <= ${hi}; ${v}++) {`;
      }
    }
    if (domain === "bigint") {
      const { lo, hi } = bigintBounds(range ?? {});
      if (lo !== undefined && hi !== undefined)
        return `for (let ${v} = ${lo}n; ${v} <= ${hi}n; ${v}++) {`;
    }
  }
  throw new Error(`binder '${v}' is not enumerable`);
}

/** Every loop a binder opens: one for a primitive, one per leaf slot of a
 * class binder's constructor tree, depth first, so the walk is ascending
 * lexicographic over the flattened argument tuple. */
export function loopHeaders(binder: Binder): string[] {
  if (!isClassDomain(binder.domain)) return [loopHeader(binder)];
  return leaves(binder).map((leaf) => loopHeader(leaf));
}

/** The nested argument tuple a class binder's constructor takes, spelled
 * with the leaf loop variables so the sampled path's construction and
 * rendering apply to it unchanged. */
export function argsTuple(varName: string, domain: ClassCtorDomain): string {
  return tupleOf(domain, `__${varName}`);
}

/** The loop variable of leaf slot `i` under `prefix`: one path segment per
 * nesting level, so no two slots of one binder share a name. */
function leafName(prefix: string, i: number): string {
  return `${prefix}_${i}`;
}

function slots(domain: ClassCtorDomain): CtorParam[] {
  if (domain.ctorParams === undefined)
    throw new Error(
      `unresolved class binder '${domain.className}' reached enumeration`,
    );
  return domain.ctorParams;
}

function leaves(binder: Binder): Binder[] {
  const out: Binder[] = [];
  const walk = (domain: ClassCtorDomain, prefix: string) => {
    slots(domain).forEach((p, i) => {
      if (isClassCtorDomain(p.domain)) walk(p.domain, leafName(prefix, i));
      else out.push({ varName: leafName(prefix, i), domain: p.domain });
    });
  };
  walk(binder.domain as ClassCtorDomain, `__${binder.varName}`);
  return out;
}

function tupleOf(domain: ClassCtorDomain, prefix: string): string {
  const parts = slots(domain).map((p, i) =>
    isClassCtorDomain(p.domain)
      ? tupleOf(p.domain, leafName(prefix, i))
      : leafName(prefix, i),
  );
  return `[${parts.join(", ")}]`;
}

/** A plain test that walks the domain: nested ascending loops in binder
 * order, so the first failure is the least tuple. A class binder's loops
 * range over its constructor slots; the instance is built once the tuple
 * is counted, and a throwing tuple is skipped as denoting no instance.
 * Preconditions and the body share one try so anything they throw
 * reports as `threw`. */
export function emitEnumerated(
  s: PropertySpec,
  cases: number,
  sourceFile: string,
  indent: string,
): string {
  const name = JSON.stringify(s.name);
  const file = JSON.stringify(sourceFile);
  const fn = JSON.stringify(
    qualifiedName(s.functionName, s.className, s.isStatic),
  );
  const ident = `${file}, ${fn}, ${name}`;
  const shapes = s.binders.map((b) =>
    isClassDomain(b.domain) ? ctorShape(b.domain) : null,
  );
  const vars = s.binders
    .map((b, i) => (shapes[i] === null ? b.varName : `__args_${b.varName}`))
    .join(", ");
  const varNames = s.binders.map((b) => JSON.stringify(b.varName)).join(", ");
  const ctors = shapes.some((c) => c !== null)
    ? `, [${shapes.map((c) => JSON.stringify(c)).join(", ")}]`
    : "";
  const out: string[] = [];
  out.push(`${indent}test(${name}, { timeout: ${TEST_TIMEOUT_MS} }, () => {`);
  out.push(
    `${indent}  const __fail = (__cx: unknown[], __e: { message?: string } | null) => ${REPORT_ALIAS}(${ident}, [${varNames}], { failed: true, counterexample: __cx, errorInstance: __e }${ctors});`,
  );
  out.push(`${indent}  const __t0 = performance.now();`);
  out.push(`${indent}  let __done = 0;`);
  let inner = `${indent}  `;
  let depth = 0;
  for (const b of s.binders) {
    for (const header of loopHeaders(b)) {
      out.push(`${inner}${header}`);
      inner += "  ";
      depth++;
    }
  }
  if (depth === 0) {
    // Only zero-argument constructors: one tuple, but the skips below are
    // `continue`s and need an iteration statement to leave.
    out.push(`${inner}for (const __once of [0]) {`);
    inner += "  ";
    depth++;
  }
  out.push(
    `${inner}if (performance.now() - __t0 > ${LOOP_BUDGET_MS}) ${BUDGET_ALIAS}(${ident}, __done, ${cases});`,
  );
  out.push(`${inner}__done++;`);
  for (const b of s.binders) {
    if (!isClassDomain(b.domain)) continue;
    const v = b.varName;
    const cls = b.domain.className;
    const call = ctorCall(cls, b.domain.ctorParams!, `__args_${v}`);
    out.push(`${inner}const __args_${v} = ${argsTuple(v, b.domain)};`);
    out.push(`${inner}let ${v}!: ${cls};`);
    out.push(`${inner}try { ${v} = ${call}; } catch { continue; }`);
  }
  out.push(`${inner}let __r = false;`);
  out.push(`${inner}try {`);
  for (const p of s.preconditions) out.push(`${inner}  if (!(${p})) continue;`);
  out.push(`${inner}  __r = (${s.body});`);
  out.push(`${inner}} catch (__e) {`);
  out.push(
    `${inner}  __fail([${vars}], __e instanceof Error ? __e : { message: String(__e) });`,
  );
  out.push(`${inner}}`);
  out.push(`${inner}if (!__r) __fail([${vars}], null);`);
  for (let i = 0; i < depth; i++) {
    inner = inner.slice(0, -2);
    out.push(`${inner}}`);
  }
  out.push(`${indent}});`);
  return out.join("\n");
}
