import { helper } from "../lib/helper.js";
/** @ensures{p} forall (x: int ∈ [0, 5)) { helper(f(x)) >= 0 } */
export function f(x: number): number {
  return x + helper(x);
}
