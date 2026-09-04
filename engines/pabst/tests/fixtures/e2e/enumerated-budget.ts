/** 1000 cases at 20 ms each far outrun the loop budget.
 *
 * @ensures{slow} forall (n: int ∈ [1, 1000]) { crawl(n) >= 0 }
 */
export function crawl(n: number): number {
  const until = Date.now() + 20;
  while (Date.now() < until) {}
  return n;
}
