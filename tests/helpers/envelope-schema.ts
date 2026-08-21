import { schemaValidator } from "./schema-validator.js";

/** Fail the current test if `value` does not match the envelope JSON Schema. */
export const expectValidEnvelope = schemaValidator(
  new URL("../../schemas/envelope.schema.json", import.meta.url),
  "envelope",
);
