import { describe, expect, test } from "vitest";
import { parseBody } from "../../../../lemma/src/index.js";
import { chainReading, connectiveJs } from "../src/readings.js";

describe("connectiveJs", () => {
  test.each([
    ["an atom", "f(x) >= 0", "f(x) >= 0"],
    ["a disjunction", "x === 0 ∨ x === 1", "(x === 0) || (x === 1)"],
    ["a conjunction", "f(x) > x ∧ f(x) > 0", "(f(x) > x) && (f(x) > 0)"],
    ["a negation", "¬(f(x) > 100)", "!(f(x) > 100)"],
    [
      "a nested mix keeps the tree's grouping",
      "¬(x === 0 ∨ x === 1) ∧ f(x) > 0",
      "(!((x === 0) || (x === 1))) && (f(x) > 0)",
    ],
    [
      "a negated equation is the text ≢ desugars to",
      "¬(f(x) ≡ 1)",
      "!(Object.is(f(x), 1))",
    ],
  ])("%s composes as JS", (_label, body, js) => {
    expect(connectiveJs(parseBody(body))).toBe(js);
  });

  test.each([
    ["a biconditional", "f(x) > 0 ↔ x > 0"],
    ["a nested implication", "(x > 0 → f(x) > 0) ∨ x === 0"],
  ])("%s has no reading", (_label, body) => {
    expect(connectiveJs(parseBody(body))).toBeUndefined();
  });
});

describe("chainReading", () => {
  test("a connective body is one conclusion", () => {
    expect(chainReading(parseBody("f(x) > x ∧ f(x) > 0"))).toEqual({
      guards: [],
      conclusion: "(f(x) > x) && (f(x) > 0)",
    });
  });

  test("a connective antecedent is one guard", () => {
    expect(chainReading(parseBody("x === 0 ∨ x === 1 → f(x) <= 2"))).toEqual({
      guards: ["(x === 0) || (x === 1)"],
      conclusion: "f(x) <= 2",
    });
  });

  test("each antecedent of a chain is its own guard", () => {
    expect(
      chainReading(parseBody("x > 0 → x < 5 ∧ x !== 3 → f(x) > 0")),
    ).toEqual({
      guards: ["x > 0", "(x < 5) && (x !== 3)"],
      conclusion: "f(x) > 0",
    });
  });

  test.each([
    ["a biconditional body", "f(x) > 0 ↔ x > 0"],
    ["a biconditional guard", "(f(x) > 0 ↔ x > 0) → f(x) >= 0"],
    ["a nested implication in a conclusion", "x > 0 → (x > 1 → f(x) > 1)"],
  ])("%s is undefined", (_label, body) => {
    expect(chainReading(parseBody(body))).toBeUndefined();
  });
});
