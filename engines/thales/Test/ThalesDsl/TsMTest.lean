import ThalesDsl.TsM

open ThalesDsl

-- TsM is computable and comparable: pure arithmetic runs to a value.
#guard decide ((pure 5 : TsM Int) = .ok 5)
#guard decide ((pure (2 + 3) : TsM Int) = (pure 5 : TsM Int))
#guard decide ((TsM.throw (.error "boom") : TsM Int) ≠ .ok 0)

-- ballIco decides bounded ∀ over half-open Int ranges.
#guard decide (ballIco 0 3 fun x => x < 3)
#guard !decide (ballIco 0 4 fun x => x < 3)
#guard decide (ballIco (-2) 2 fun x => x * x ≤ 4)
-- Empty range is vacuously true.
#guard decide (ballIco 5 5 fun _ => False)
-- Nested ballIco (the shape multi-binder properties elaborate to).
#guard decide (ballIco 0 5 fun a => ballIco 0 5 fun b => a + b = b + a)
