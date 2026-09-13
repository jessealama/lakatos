/** 1000 cases at 2 ms each far outrun a 40 ms loop budget.
 *
 * @ensures{slow} forall (n: int ∈ [1, 1000]) { crawl(n) >= 0 }
 */
export function crawl(n: number): number {
  const until = Date.now() + 2;
  while (Date.now() < until) {}
  return n;
}
