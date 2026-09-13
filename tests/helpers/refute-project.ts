import * as fs from "node:fs";
import * as path from "node:path";
import { DEFAULT_TSCONFIG } from "./cli.js";
import { RUN_ROOT, TYPECHECK_CACHE } from "../../src/run-dir.js";

/** The README-usage project the refute CLI suites run in: two annotated
 * files, one plain, one class, and the input-error, stacked, and guarded
 * cases. Lives inside the repo tree because generated tests import
 * "lakatos/runtime" through the package self-reference. */
export function seedRefuteProject(dir: string): void {
  fs.rmSync(dir, { recursive: true, force: true });
  fs.mkdirSync(dir, { recursive: true });
  fs.writeFileSync(
    path.join(dir, "good.ts"),
    `/** @ensures{nonneg} forall (n: nat) { good(n) >= 0 } */\nexport function good(n: number): number { return n; }\n`,
    "utf8",
  );
  fs.writeFileSync(
    path.join(dir, "bad.ts"),
    `/** @ensures{negative} forall (n: nat) { bad(n) < 0 } */\nexport function bad(n: number): number { return n; }\n`,
    "utf8",
  );
  fs.writeFileSync(path.join(dir, "tsconfig.json"), DEFAULT_TSCONFIG);
  fs.writeFileSync(
    path.join(dir, "plain.ts"),
    `export function plain(n: number): number { return n; }\n`,
    "utf8",
  );
  // In a subdirectory: the `*.ts` glob case below counts the top-level
  // fixtures, and a fourth one there would change its arithmetic.
  fs.mkdirSync(path.join(dir, "klass"), { recursive: true });
  fs.writeFileSync(
    path.join(dir, "klass", "box.ts"),
    `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{roundTrip} forall (x: number) { Object.is(new Box(x).v, x) } */
  get v(): number {
    return this.#v;
  }
}
`,
    "utf8",
  );
  fs.mkdirSync(path.join(dir, "inputerr"), { recursive: true });
  fs.writeFileSync(
    path.join(dir, "inputerr", "mixed.ts"),
    `class Hidden {
  /** @ensures{p} forall (x: int) { Hidden.id(x) === x } */
  static id(x: number): number { return x; }
}

/** @ensures{q} forall (x: int ∈ [0, 5)) { ok(x) === x } */
export function ok(x: number): number { return x; }
`,
    "utf8",
  );
  // One JSDoc block per property. The first property is false, so a run
  // that dropped it would exit 0 with a clean envelope.
  fs.mkdirSync(path.join(dir, "stacked"), { recursive: true });
  fs.writeFileSync(
    path.join(dir, "stacked", "keep.ts"),
    `/** @ensures{tooBig} forall (n: int ∈ [0, 10)) { keep(n) >= 5 } */
/** @ensures{atLeastOne} forall (n: int ∈ [0, 10)) { keep(n) >= 1 } */
export function keep(n: number): number {
  return n + 1;
}
`,
    "utf8",
  );
  // Three guards discard ~88% of samples; an infinite factor makes the
  // conclusion NaN. Under seed 2 fast-check's default 100 runs pass
  // cleanly, so this pins the larger budget refute runs with.
  fs.mkdirSync(path.join(dir, "guarded"), { recursive: true });
  fs.writeFileSync(
    path.join(dir, "guarded", "conv.ts"),
    `/**
 * @ensures{naiveMonotone} forall (x y sf so tf to: number) {
 *   0 < sf → 0 < tf → x <= y →
 *     conv(x, sf, so, tf, to) <= conv(y, sf, so, tf, to)
 * }
 */
export function conv(v: number, sf: number, so: number, tf: number, to: number): number {
  return (v * sf + so - to) / tf;
}
`,
    "utf8",
  );
}

/** Every run directory goes; the typecheck cache stays, so a test pays a
 * cold tsc program only when it made the project stale itself. */
export function clearRunDirs(dir: string): void {
  const root = path.join(dir, RUN_ROOT);
  if (!fs.existsSync(root)) return;
  for (const entry of fs.readdirSync(root)) {
    if (entry === TYPECHECK_CACHE) continue;
    fs.rmSync(path.join(root, entry), { recursive: true, force: true });
  }
}
