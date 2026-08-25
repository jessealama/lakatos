import { scale } from '@example/units';

/** @ensures{nonNegative} forall (x: int ∈ [0, 10)) { grow(x) >= 0 } */
export function grow(x: number): number {
  return scale(x);
}
