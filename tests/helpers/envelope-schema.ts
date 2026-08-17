import { readFileSync } from "node:fs";
import { Ajv } from "ajv";
import { expect } from "vitest";

const schemaPath = new URL(
  "../../schemas/envelope.schema.json",
  import.meta.url,
).pathname;
const schema = JSON.parse(readFileSync(schemaPath, "utf8"));
const ajv = new Ajv({ allErrors: true });
const validate = ajv.compile(schema);

/** Fail the current test if `value` does not match the envelope JSON Schema. */
export function expectValidEnvelope(value: unknown): void {
  if (!validate(value)) {
    expect.fail(
      `envelope failed schema validation: ${ajv.errorsText(validate.errors)}\n` +
        JSON.stringify(value, null, 2),
    );
  }
}
