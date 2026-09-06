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
  it("returns the body's value", async () => {
    expect(await withInterruptGuard(async () => "verdicts")).toBe("verdicts");
  });

  it("guards every covered signal, and only while the body runs", async () => {
    const before = guardCounts();
    await withInterruptGuard(async () => {
      expect(guardCounts()).toEqual(before.map((n) => n + 1));
    });
    expect(guardCounts()).toEqual(before);
  });

  it("disarms even when the body throws", async () => {
    const before = guardCounts();
    await expect(
      withInterruptGuard(async () => {
        throw new Error("boom");
      }),
    ).rejects.toThrow("boom");
    expect(guardCounts()).toEqual(before);
  });

  it.each([...INTERRUPT_SIGNALS])(
    "reports %s when it reached this process during the body",
    async (s) => {
      // The signal is delivered while the body runs, as a group signal
      // is during spawnSync; the listener can only fire once the loop
      // turns, which is what `interrupted` waits for.
      const seen = await withInterruptGuard(async (interrupted) => {
        process.kill(process.pid, s);
        return interrupted();
      });
      expect(seen).toBe(s);
    },
  );

  it("reports nothing when no signal arrived", async () => {
    const seen = await withInterruptGuard(async (interrupted) => interrupted());
    expect(seen).toBeUndefined();
  });

  it("keeps the first signal: a second Ctrl-C does not change the report", async () => {
    const seen = await withInterruptGuard(async (interrupted) => {
      process.kill(process.pid, "SIGINT");
      process.kill(process.pid, "SIGTERM");
      return interrupted();
    });
    expect(seen).toBe("SIGINT");
  });
});
