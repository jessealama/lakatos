export function boom(x: number): number {
  throw new RangeError("the arm the condition passes over never runs");
}

/** @ensures{thenWins} forall (x: int in [0, 4)) { pick(x) === 0 } */
export function pick(x: number): number {
  return x === x ? 0 : boom(x);
}

/** @ensures{elseWins} forall (x: int in [0, 4)) { pickElse(x) === 1 } */
export function pickElse(x: number): number {
  return x === x + 1 ? boom(x) : 1;
}
