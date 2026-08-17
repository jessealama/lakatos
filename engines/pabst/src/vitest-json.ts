/** The subset of vitest's JSON reporter output the envelope consumes. */
export interface AssertionResult {
  status: string;
  failureMessages: string[];
}
export interface FileResult {
  status?: string;
  message?: string;
  assertionResults: AssertionResult[];
}
export interface VitestJson {
  numPassedTests: number;
  numFailedTests: number;
  success: boolean;
  testResults: FileResult[];
}
