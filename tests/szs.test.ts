import { describe, it, expect } from "vitest";
import { szsForIssue } from "../src/szs.js";

describe("szsForIssue", () => {
  it("maps falsified to CounterSatisfiable", () => {
    expect(szsForIssue("falsified")).toBe("CounterSatisfiable");
  });

  it("maps threw to Error", () => {
    expect(szsForIssue("threw")).toBe("Error");
  });

  it("maps exhausted to GaveUp", () => {
    expect(szsForIssue("exhausted")).toBe("GaveUp");
  });
});
