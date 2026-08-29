const millisecondsInSecond = 1000;

/** @ensures{nonNegative} forall (s: int ∈ [0, 10)) { secondsToMilliseconds(s) >= 0 } */
export function secondsToMilliseconds(seconds: number): number {
  return seconds * millisecondsInSecond;
}

/** @ensures{bounded} forall (s: int ∈ [0, 5)) { keepBelowSecond(s) <= millisecondsInSecond } */
export function keepBelowSecond(s: number): number {
  return s;
}
