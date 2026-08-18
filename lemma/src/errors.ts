/**
 * A user-facing error: the input (an annotation, formula, or reference) is
 * at fault, not the tool. The CLI catches these and reports them as exit 2
 * with a one-line diagnostic. Anything else escaping the compile front-end
 * is an internal bug and crashes loudly.
 */
export class LemmaError extends Error {
  override name = "LemmaError";
}
