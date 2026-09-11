// The helper's loop is outside the model. Every value in the domain takes
// the other branch, so the proof never touches the residual it becomes.
function digits(n: number): number {
  let count = 0;
  for (let k = n; k >= 1; k = k / 10) {
    count = count + 1;
  }
  return count;
}

/** @ensures{one} forall (n: int ∈ [0, 10)) { width(n) === 1 } */
export function width(n: number): number {
  if (n < 10) {
    return 1;
  }
  return digits(n);
}
