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
 * process before it can report. The run is synchronous, so a signal that
 * lands during it is delivered only once the event loop turns:
 * `interrupted` lets it turn and answers with the first covered signal
 * that reached this process. That, not the child's death, is what a run
 * reads: an engine may catch the signal and exit by status (vitest exits
 * 130) rather than die of it. Outside the guard the default disposition
 * stands, and lakatos dies where it could not have reported anyway.
 */
export async function withInterruptGuard<T>(
  body: (interrupted: () => Promise<InterruptSignal | undefined>) => Promise<T>,
): Promise<T> {
  let seen: InterruptSignal | undefined;
  const record = (s: NodeJS.Signals): void => {
    seen ??= s as InterruptSignal;
  };
  const interrupted = async (): Promise<InterruptSignal | undefined> => {
    // A pending signal is read in the poll phase. An immediate scheduled
    // from a poll callback runs in the same iteration's check phase, so a
    // second one is what guarantees a fresh poll in between.
    for (let i = 0; i < 2; i++)
      await new Promise<void>((resolve) => setImmediate(resolve));
    return seen;
  };
  for (const s of INTERRUPT_SIGNALS) process.on(s, record);
  try {
    return await body(interrupted);
  } finally {
    for (const s of INTERRUPT_SIGNALS) process.off(s, record);
  }
}
