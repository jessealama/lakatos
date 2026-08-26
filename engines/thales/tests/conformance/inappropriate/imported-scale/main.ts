// Refused for now: the emission pipeline does not yet follow relative
// import closures, so the imported callee degrades this entry. This
// fixture returns to the theorem bucket when import emission lands.
import { double } from "./scale.js";

/** @ensures{quadruples} forall (x: int ∈ [0, 20)) { twice(x) === 4 * x } */
export function twice(x: number): number {
  return double(x) + double(x);
}
