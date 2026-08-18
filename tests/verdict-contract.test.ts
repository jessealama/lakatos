import { describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { PROVE_STATUSES } from "../src/envelope.js";

const scriptPath = fileURLToPath(
  new URL(
    "../engines/thales/scripts/check-verdict-channel.js",
    import.meta.url,
  ),
);

describe("verdict-channel contract", () => {
  it("the engine-side check allowlists exactly the CLI's statuses", () => {
    const script = readFileSync(scriptPath, "utf8");
    const m = script.match(/const SZS = new Set\(\[([^\]]+)\]\)/);
    expect(m, "SZS set literal not found").not.toBeNull();
    const names = [...m![1]!.matchAll(/'([^']+)'/g)].map((x) => x[1]!);
    expect(new Set(names)).toEqual(new Set(PROVE_STATUSES));
  });
});
