const s = 1000;
const m = s * 60;

/** @ensures{nonNegative} forall (x: int ∈ [0, 10)) { toMinutes(x) >= 0 } */
export function toMinutes(x: number): number {
  return x * m;
}
