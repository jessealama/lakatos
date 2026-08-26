import { double } from "./scale.js";

/** @ensures{quadruples} forall (x: int ∈ [0, 20)) { twice(x) === 4 * x } */
export function twice(x: number): number {
  return double(x) + double(x);
}
