import { expect } from "vitest";
import { LemmaError } from "../../src/errors.js";

/**
 * Assert that `fn` throws a LemmaError matching `match`. The class matters
 * as much as the message: only LemmaError maps to the CLI's exit-2 error
 * mode, so a throw site regressing to plain Error breaks the exit-code
 * contract even if its message survives.
 */
export function expectLemmaError(
  fn: () => unknown,
  match: RegExp | string,
): void {
  expect(fn).toThrow(LemmaError);
  expect(fn).toThrow(match);
}
