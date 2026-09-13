/** The config every child vitest runs under: vitest's defaults, nothing
 * inherited from the cwd's tree, so a project's own config cannot reach
 * into a refutation run and this repo's global setup cannot rebuild dist/
 * underneath one. */
export default { test: {} };
