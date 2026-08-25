/** @type {import('@stryker-mutator/api/core').PartialStrykerOptions} */
export default {
  testRunner: "command",
  commandRunner: {
    command: "./node_modules/.bin/vitest run --bail 1",
  },
  mutate: ["src/**/*.ts", "engines/pabst/src/**/*.ts", "!**/*.d.ts"],
  ignorePatterns: [".lakatos", "coverage", "reports", "engines/thales"],
  concurrency: 8,
  timeoutFactor: 3,
  timeoutMS: 60000,
  disableTypeChecks: "{src,engines/pabst/src}/**/*.ts",
  reporters: ["clear-text", "html", "progress"],
};
