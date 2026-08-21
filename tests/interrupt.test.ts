import { describe, it, expect } from "vitest";
import {
  INTERRUPT_SIGNALS,
  interruptedBy,
  withInterruptGuard,
} from "../src/interrupt.js";

const guardCounts = (): number[] =>
  INTERRUPT_SIGNALS.map((s) => process.listenerCount(s));

describe("interruptedBy", () => {
  it.each([...INTERRUPT_SIGNALS])("reads %s off the child's death", (s) => {
    expect(interruptedBy({ signal: s })).toBe(s);
  });

  it("ignores a signal the contract does not cover", () => {
    expect(interruptedBy({ signal: "SIGKILL" })).toBeUndefined();
    expect(interruptedBy({ signal: "SIGSEGV" })).toBeUndefined();
  });

  it("ignores a child that died of its own accord", () => {
    expect(interruptedBy({ signal: null })).toBeUndefined();
    expect(interruptedBy({})).toBeUndefined();
  });

  it("ignores a timeout kill: the engine's budget, not the user's request", () => {
    // spawnSync kills a timed-out child with SIGTERM and reports ETIMEDOUT
    // beside it; reading that as an interruption would turn every Lean
    // timeout into a User verdict.
    const error = Object.assign(new Error("spawnSync lake ETIMEDOUT"), {
      code: "ETIMEDOUT",
    });
    expect(interruptedBy({ signal: "SIGTERM", error })).toBeUndefined();
  });
});

describe("withInterruptGuard", () => {
  it("returns the body's value", () => {
    expect(withInterruptGuard(() => "verdicts")).toBe("verdicts");
  });

  it("guards every covered signal, and only while the body runs", () => {
    const before = guardCounts();
    withInterruptGuard(() => {
      expect(guardCounts()).toEqual(before.map((n) => n + 1));
    });
    expect(guardCounts()).toEqual(before);
  });

  it("disarms even when the body throws", () => {
    const before = guardCounts();
    expect(() =>
      withInterruptGuard(() => {
        throw new Error("boom");
      }),
    ).toThrow("boom");
    expect(guardCounts()).toEqual(before);
  });

  it("installs listeners that do nothing: they exist only to keep the default disposition from killing the run", () => {
    withInterruptGuard(() => {
      for (const s of INTERRUPT_SIGNALS) {
        const guard = process.listeners(s).at(-1)!;
        expect(guard(s)).toBeUndefined();
      }
    });
  });
});
