/** One tuple, slower than the loop budget: the walk still finishes.
 *
 * @ensures{slow} forall (n: int ∈ [1, 1]) { crawl(n) >= 1 }
 */
export function crawl(n: number): number {
  const until = Date.now() + 9000;
  while (Date.now() < until) {}
  return n;
}
