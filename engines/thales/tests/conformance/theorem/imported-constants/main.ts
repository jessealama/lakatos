import { daysInWeek } from "./constants.js";

/** @ensures{nonNegative} forall (d: int ∈ [0, 70)) { daysToWeeks(d) >= 0 } */
export function daysToWeeks(days: number): number {
  return days / daysInWeek;
}
