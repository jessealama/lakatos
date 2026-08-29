import { fileURLToPath } from "node:url";
import { defineConfig } from "vitest/config";

export default defineConfig({
  test: {
    include: [
      "tests/**/*.test.ts",
      "lemma/tests/**/*.test.ts",
      "engines/pabst/tests/**/*.test.ts",
      "engines/thales/frontend/tests/**/*.test.ts",
      ".lakatos/**/*.test.ts",
    ],
    // Absolute: refute spawns vitest from a project directory that may sit
    // inside this repo, and such a run inherits this config — a relative
    // path would resolve against *its* root, where the file is not.
    globalSetup: [
      fileURLToPath(new URL("./tests/global-setup.ts", import.meta.url)),
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
        "engines/thales/frontend/src/**/*.ts",
      ],
      exclude: ["**/*.test.ts", "**/*.d.ts"],
      reporter: ["text", "html"],
      thresholds: {
        // Ratchet: when coverage rises, Vitest rewrites these numbers
        // upward in this file; if it drops below, the run fails. Seeded
        // from the baseline on 2026-08-17 — bump only happens via
        // autoUpdate. Reseeded 2026-08-26 after the transcriber's deletion
        // changed the denominator; emission.ts still carries two defensive
        // branches no input can reach. Reseeded 2026-08-29: the shared
        // parse gate refuses every unreadable formula before any spine
        // runs, so the enumeration's own rethrow and the emitter's bare
        // fallthrough joined that unreachable set.
        autoUpdate: true,
        statements: 99.39,
        branches: 98.31,
        functions: 100,
        lines: 99.61,
      },
    },
  },
});
