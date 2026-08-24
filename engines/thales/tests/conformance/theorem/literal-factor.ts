/**
 * @ensures{monotone} forall (x y: number) {
 *   x <= y → cmToInch(x) <= cmToInch(y)
 * }
 */
export function cmToInch(value: number): number {
  return value / 2.54;
}

/**
 * @ensures{monotone} forall (x y: number) {
 *   x <= y → triple(x) <= triple(y)
 * }
 */
export function triple(value: number): number {
  return value * 3;
}
