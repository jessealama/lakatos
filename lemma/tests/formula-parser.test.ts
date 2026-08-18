import { describe, it } from "vitest";
import { parseBody } from "../src/formula-parser.js";
import { expectLemmaError } from "./helpers/errors.js";

// What parseBody produces for accepted input is asserted through lowering
// in pabst's parse-lower tests; here only the parser's rejections.

describe("parseBody — equation errors", () => {
  it("rejects loose ==", () => {
    expectLemmaError(() => parseBody("a == b"), /loose equality/);
  });
  it("rejects loose !=", () => {
    expectLemmaError(() => parseBody("a != b"), /loose inequality/);
  });
  it("rejects = assignment with a ≡ hint", () => {
    expectLemmaError(() => parseBody("x = 0"), /write A ≡ B/);
  });
  it("rejects ≠ with a ≢ hint", () => {
    expectLemmaError(() => parseBody("a ≠ b"), /write ≢/);
  });
  it("rejects chained equations", () => {
    expectLemmaError(() => parseBody("a ≡ b ≡ c"), /chained equations/);
  });
});

describe("parseBody — errors", () => {
  it("rejects a chained ↔", () => {
    expectLemmaError(() => parseBody("a ↔ b ↔ c"), /parenthesi[sz]e/i);
  });
  it("rejects a top-level JS && with a glyph hint", () => {
    expectLemmaError(() => parseBody("a && b"), /use ∧/);
  });
  it("rejects a top-level JS || with a glyph hint", () => {
    expectLemmaError(() => parseBody("a || b"), /use ∨/);
  });
  it("rejects a top-level prefix ! with a glyph hint", () => {
    expectLemmaError(() => parseBody("!p"), /use ¬/);
    expectLemmaError(() => parseBody("!Object.is(a, b)"), /use ¬/);
  });
  it("rejects an empty operand", () => {
    expectLemmaError(() => parseBody("a ∧ "), /empty/i);
  });
});
