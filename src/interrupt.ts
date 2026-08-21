/**
 * The termination signals a lakatos run can still report on. Each is
 * catchable, and each is delivered to the whole foreground process group
 * — Ctrl-C at the terminal, a supervisor's kill, a CI cancel — so the
 * engine's child dies of the same signal and the run learns of it from
 * the child's death. SIGKILL is out of contract: nothing can be printed.
 */
export const INTERRUPT_SIGNALS = ["SIGINT", "SIGTERM", "SIGHUP"] as const;

export type InterruptSignal = (typeof INTERRUPT_SIGNALS)[number];

/** What interruption detection needs from a spawn; a subset of
 * spawnSync's return. */
export interface SignalOutcome {
  signal?: NodeJS.Signals | null;
  error?: Error;
}

/** The signal that stopped a child at the user's request, if any. A
 * spawn error means the runner's own failure paths own the outcome: a
 * timed-out artifact is killed with SIGTERM too, but carries ETIMEDOUT
 * beside it, and the engine's budget must not be reported as the user's
 * doing. */
export function interruptedBy(r: SignalOutcome): InterruptSignal | undefined {
  if (r.error !== undefined || r.signal === undefined || r.signal === null)
    return undefined;
  const signals: readonly string[] = INTERRUPT_SIGNALS;
  return signals.includes(r.signal) ? (r.signal as InterruptSignal) : undefined;
}

/**
 * Run `body` with the default signal disposition disarmed, so a
 * termination signal kills the engine's child without killing this
 * process before it can report. The listeners deliberately do nothing:
 * lakatos runs synchronously, so their callbacks cannot run until the
 * event loop turns, which is after the run has already exited — what
 * the run reads instead is the child's death by signal. Outside this
 * window the default disposition stands, and lakatos dies where it
 * could not have reported anyway.
 */
export function withInterruptGuard<T>(body: () => T): T {
  const ignore = (): void => {};
  for (const s of INTERRUPT_SIGNALS) process.on(s, ignore);
  try {
    return body();
  } finally {
    for (const s of INTERRUPT_SIGNALS) process.off(s, ignore);
  }
}
