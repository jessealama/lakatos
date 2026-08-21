import { describe, it, expect } from "vitest";
import { parseBody } from "../../../lemma/src/index.js";
import { lowerTop } from "../src/lower.js";

// Lower the parsed AST to a string so assertions read clearly.
const lo = (s: string) => lowerTop(parseBody(s));

describe("parse + lower — precedence", () => {
  it("¬ binds tighter than ∧ binds tighter than ∨", () => {
    expect(lo("¬a ∧ b ∨ c")).toEqual({
      preconditions: [],
      body: '((!(__bool(a, "a")) && __bool(b, "b")) || __bool(c, "c"))',
    });
  });
  it("→ is looser than ∨ and routes the antecedent to a precondition (top level)", () => {
    expect(lo("a ∨ b → c")).toEqual({
      preconditions: ['(__bool(a, "a") || __bool(b, "b"))'],
      body: '__bool(c, "c")',
    });
  });
  it("a → chain makes each antecedent a precondition", () => {
    expect(lo("a → b → c")).toEqual({
      preconditions: ['__bool(a, "a")', '__bool(b, "b")'],
      body: '__bool(c, "c")',
    });
  });
  it("parenthesised → is nested/material, not a precondition", () => {
    expect(lo("(a → b) ∧ c")).toEqual({
      preconditions: [],
      body: '((!(__bool(a, "a")) || __bool(b, "b")) && __bool(c, "c"))',
    });
  });
  it("↔ is loosest and lowers to ===", () => {
    expect(lo("a ∧ b ↔ c")).toEqual({
      preconditions: [],
      body: '((__bool(a, "a") && __bool(b, "b")) === __bool(c, "c"))',
    });
  });
});

describe("parse + lower — atoms keep their JS", () => {
  it("treats a call with commas as one atom", () => {
    expect(lo("f(x, y) !== 0")).toEqual({
      preconditions: [],
      body: '__bool(f(x, y) !== 0, "f(x, y) !== 0")',
    });
  });
  it("allows nested && inside a callback leaf", () => {
    expect(lo("xs.every(x => x > 0 && x < 10)")).toEqual({
      preconditions: [],
      body: '__bool(xs.every(x => x > 0 && x < 10), "xs.every(x => x > 0 && x < 10)")',
    });
  });
  it("keeps a connective glyph inside template text within one atom", () => {
    expect(lo("p(`${a} ∧ ${b}`)")).toEqual({
      preconditions: [],
      body: '__bool(p(`${a} ∧ ${b}`), "p(`${a} ∧ ${b}`)")',
    });
  });
  it("keeps a connective inside a template substitution within one atom", () => {
    expect(lo("`${a ∧ b}` === s")).toEqual({
      preconditions: [],
      body: '__bool(`${a ∧ b}` === s, "`${a ∧ b}` === s")',
    });
  });
});

describe("parse + lower — equations", () => {
  it("lowers ≡ to Object.is, labeled with the original text", () => {
    expect(lo("negate(x) ≡ 0 - x")).toEqual({
      preconditions: [],
      body: '__bool(Object.is(negate(x), 0 - x), "negate(x) ≡ 0 - x")',
    });
  });
  it("handles an equation LHS that is not a JS assignment target", () => {
    expect(lo("x ≢ -0 -> x + 0 ≡ x")).toEqual({
      preconditions: ['__bool(!Object.is(x, -0), "x ≢ -0")'],
      body: '__bool(Object.is(x + 0, x), "x + 0 ≡ x")',
    });
  });
  it("lowers ≢ to !Object.is", () => {
    expect(lo("x ≢ y")).toEqual({
      preconditions: [],
      body: '__bool(!Object.is(x, y), "x ≢ y")',
    });
  });
  it("negates an equation with formula-level ¬", () => {
    expect(lo("¬(x ≡ y)")).toEqual({
      preconditions: [],
      body: '!(__bool(Object.is(x, y), "x ≡ y"))',
    });
  });
  it("allows JS ! on an equation side (the ¬ rule judges the desugared atom)", () => {
    expect(lo("!x ≡ y")).toEqual({
      preconditions: [],
      body: '__bool(Object.is(!x, y), "!x ≡ y")',
    });
    expect(lo("(!x) ≡ y")).toEqual({
      preconditions: [],
      body: '__bool(Object.is((!x), y), "(!x) ≡ y")',
    });
  });
});
