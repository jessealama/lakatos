import { defineConfig } from "vitest/config";

export default defineConfig({
  test: {
    include: [
      "tests/**/*.test.ts",
      "lemma/tests/**/*.test.ts",
      "engines/pabst/tests/**/*.test.ts",
      ".pabst/**/*.test.ts",
    ],
    coverage: {
      provider: "v8",
      // Count every source file, even ones no test imports, so untested
      // code drags the baseline down instead of hiding from the ratchet.
      all: true,
      include: [
        "src/**/*.ts",
        "lemma/src/**/*.ts",
        "engines/pabst/src/**/*.ts",
      ],
      exclude: ["**/*.test.ts", "**/*.d.ts"],
      reporter: ["text", "html"],
      thresholds: {
        // Ratchet: when coverage rises, Vitest rewrites these numbers
        // upward in this file; if it drops below, the run fails. Seeded
        // from the baseline on 2026-08-17 — bump only happens via autoUpdate.
        autoUpdate: true,
        statements: 98.56,
        branches: 96.42,
        functions: 100,
        lines: 99.24,
      },
    },
  },
});
