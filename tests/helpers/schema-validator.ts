import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { Ajv } from "ajv";
import { expect } from "vitest";

/**
 * Compile the schema at `schemaUrl` into a checker that fails the current
 * test when its argument does not match; `label` names the thing being
 * validated in the failure message.
 */
export function schemaValidator(
  schemaUrl: URL,
  label: string,
): (value: unknown) => void {
  const schema = JSON.parse(readFileSync(fileURLToPath(schemaUrl), "utf8"));
  const ajv = new Ajv({ allErrors: true });
  const validate = ajv.compile(schema);
  return (value: unknown): void => {
    if (!validate(value)) {
      expect.fail(
        `${label} failed schema validation: ${ajv.errorsText(validate.errors)}\n` +
          JSON.stringify(value, null, 2),
      );
    }
  };
}
