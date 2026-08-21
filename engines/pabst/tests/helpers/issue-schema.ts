import { schemaValidator } from "../../../../tests/helpers/schema-validator.js";

/** Fail the current test if `issue` does not match the issue JSON Schema. */
export const expectValidIssue = schemaValidator(
  new URL("../../schemas/issue.schema.json", import.meta.url),
  "issue",
);
