import { describe, it, expect } from "vitest";
import { shardOf } from "../../scripts/shard.js";

describe("shardOf", () => {
  it("returns everything when the spec is undefined", () => {
    expect(shardOf(["a", "b", "c"], undefined)).toEqual(["a", "b", "c"]);
  });

  it("partitions round-robin so every element appears exactly once", () => {
    const items = ["a", "b", "c", "d", "e", "f", "g"];
    const shards = [
      shardOf(items, "1/3"),
      shardOf(items, "2/3"),
      shardOf(items, "3/3"),
    ];
    expect([...shards.flat()].sort()).toEqual(items);
  });

  it("balances to within one element", () => {
    const items = Array.from({ length: 100 }, (_, i) => `f${i}`);
    const sizes = [1, 2, 3].map((i) => shardOf(items, `${i}/3`).length);
    expect(Math.max(...sizes) - Math.min(...sizes)).toBeLessThanOrEqual(1);
  });

  it("refuses an out-of-range index", () => {
    expect(() => shardOf(["a"], "4/3")).toThrow(/shard index/);
  });

  it("refuses a malformed spec", () => {
    expect(() => shardOf(["a"], "half")).toThrow(/shard spec/);
  });
});
