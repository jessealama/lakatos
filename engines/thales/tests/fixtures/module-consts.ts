const millisecondsInSecond = 1000;
const safeMathAbs = Math.abs;
const millisecondsInMinute = millisecondsInSecond * 60;
const millisecondsInHour = millisecondsInMinute * 60;

/** @ensures{nonNegative} forall (s: int ∈ [0, 10)) { secondsToMilliseconds(s) >= 0 } */
export function secondsToMilliseconds(seconds: number): number {
  return seconds * millisecondsInSecond;
}

/** @ensures{nonNegative} forall (n: int ∈ [-10, 10)) { magnitude(n) >= 0 } */
export function magnitude(n: number): number {
  return safeMathAbs(n);
}

/** @ensures{bounded} forall (s: int ∈ [0, 5)) { keepBelowSecond(s) <= millisecondsInSecond } */
export function keepBelowSecond(s: number): number {
  return s;
}

/** @ensures{nonNegative} forall (h: int ∈ [0, 10)) { hoursToMilliseconds(h) >= 0 } */
export function hoursToMilliseconds(hours: number): number {
  return hours * millisecondsInHour;
}
