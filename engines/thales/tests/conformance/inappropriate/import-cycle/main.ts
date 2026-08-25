import { scaled } from './cycle.js';

// Modeled: the cycle degrades the names on the edge that closes it, not
// the entry file's own declarations.
export function base(x: number): number {
  return x + 1;
}

/** @ensures{nonNegative} forall (x: int ∈ [0, 10)) { total(x) >= 0 } */
export function total(x: number): number {
  return base(x) + scaled(x);
}
