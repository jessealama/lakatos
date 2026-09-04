import {
  type Binder,
  bigintBounds,
  intInterval,
  isClassDomain,
  prefixCardinality,
  qualifiedName,
} from "../../../lemma/src/index.js";
import { BUDGET_ALIAS, REPORT_ALIAS } from "./contract.js";
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

/** A plain test that walks the domain: nested ascending loops in binder
 * order, so the first failure is the least tuple. Preconditions and the
 * body share one try so anything they throw reports as `threw`. */
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
  const vars = s.binders.map((b) => b.varName).join(", ");
  const varNames = s.binders.map((b) => JSON.stringify(b.varName)).join(", ");
  const out: string[] = [];
  out.push(`${indent}test(${name}, { timeout: ${TEST_TIMEOUT_MS} }, () => {`);
  out.push(
    `${indent}  const __fail = (__cx: unknown[], __e: { message?: string } | null) => ${REPORT_ALIAS}(${ident}, [${varNames}], { failed: true, counterexample: __cx, errorInstance: __e });`,
  );
  out.push(`${indent}  const __t0 = performance.now();`);
  out.push(`${indent}  let __done = 0;`);
  let inner = `${indent}  `;
  for (const b of s.binders) {
    out.push(`${inner}${loopHeader(b)}`);
    inner += "  ";
  }
  out.push(
    `${inner}if (performance.now() - __t0 > ${LOOP_BUDGET_MS}) ${BUDGET_ALIAS}(${ident}, __done, ${cases});`,
  );
  out.push(`${inner}__done++;`);
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
  for (let i = 0; i < s.binders.length; i++) {
    inner = inner.slice(0, -2);
    out.push(`${inner}}`);
  }
  out.push(`${indent}});`);
  return out.join("\n");
}
