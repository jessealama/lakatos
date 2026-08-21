import { describe, it, expect } from "vitest";
import {
  isProveStatus,
  PROVE_STATUSES,
  SZS_STATUSES,
  szsForIssue,
} from "../src/szs.js";

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

describe("the prove subset", () => {
  it("is every status the prover can reach", () => {
    expect([...PROVE_STATUSES]).toEqual(
      SZS_STATUSES.filter((s) => s !== "InputError" && s !== "User"),
    );
  });

  it("excludes InputError: extraction failures never reach the prover", () => {
    expect(isProveStatus("InputError")).toBe(false);
  });

  it("excludes User: an interrupted prover reports nothing at all", () => {
    expect(isProveStatus("User")).toBe(false);
  });

  it.each([...PROVE_STATUSES])("admits %s", (status) => {
    expect(isProveStatus(status)).toBe(true);
  });

  it("rejects a status outside the vocabulary", () => {
    expect(isProveStatus("Proven")).toBe(false);
  });
});
