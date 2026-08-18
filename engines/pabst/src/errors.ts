/** Pabst's user-facing errors are the shared Lemma error class, so parse
 * errors from the shared module and engine errors stay one catchable type. */
export { LemmaError as PabstError } from "../../../lemma/src/errors.js";
