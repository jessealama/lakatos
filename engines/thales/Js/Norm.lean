import Lean
import Js.NormAttr
import Js.Number.Basic
import Js.Number.FloatFacts
import Js.Number.FloatOps
import Js.Runtime
import Js.Binders

/-! The `js_norm` simp set: normalization lemmas that strip JsM's
monadic wrapping from pure-looking goals, leaving bare Int arithmetic
for the closers, plus the binary64 facts `FloatFacts` proves — vanilla
Lean carries no float theory, so a residual goal about `Float` has none
until one lands here. Model definitions join the set at
model-elaboration time, so goals can unfold them. -/

namespace Js

open Js.Number

/-- Collapse `pure a >>= f` one bind at a time; definitional on `Except`. -/
@[js_norm] theorem jsm_pure_bind {α β : Type} (a : α) (f : α → JsM β) :
    (pure a >>= f : JsM β) = f a := rfl

/-- Two pure results are equal exactly when their values are. -/
@[js_norm] theorem jsm_pure_inj {α : Type} (a b : α) :
    ((pure a : JsM α) = pure b) ↔ a = b :=
  ⟨fun h => Except.ok.inj h, fun h => h ▸ rfl⟩

/-! A lowered `if` is a `cond` between two `JsM` computations. The set
keeps such a branch at the top of its expression — everything downstream
of it is pushed into both arms — and splits it into the two implications
its arms carry, which is what hands the closers the branch condition as a
hypothesis on the arm it selects. Only that shape lets a literal arm
reduce: while a branch sits under an operation, neither arm is a term the
ground evaluators can see. A branch both of whose arms came out as one
term collapses to that term instead of splitting, so it never reaches the
closers at all. -/

/-- What follows a branch runs in whichever arm was taken. -/
@[js_norm] theorem jsm_cond_bind {α β : Type} (c : Bool)
    (x y : JsM α) (f : α → JsM β) :
    ((bif c then x else y) >>= f) = bif c then (x >>= f) else (y >>= f) := by
  cases c <;> rfl

/-- A branch on one side of an equation is one obligation per arm. -/
@[js_norm] theorem jsm_cond_eq {α : Type} (c : Bool) (x y z : JsM α) :
    ((bif c then x else y) = z) ↔ ((c = true → x = z) ∧ (c = false → y = z)) := by
  cases c <;> simp

/-- The same split for a branch that reached the boolean island itself. -/
@[js_norm] theorem cond_eq_true_iff (c a b : Bool) :
    ((bif c then a else b) = true) ↔ ((c = true → a = true) ∧ (c = false → b = true)) := by
  cases c <;> simp

-- Boolean islands: after jsm_pure_inj, `decide P = true` becomes `P`.
attribute [js_norm] decide_eq_true_eq

/-! A guarded constructor lowers to an `ite` per guard with the whole
continuation copied into both arms, so its image is exponential in the
guards before anything reasons about it. The lemmas below flatten it back:
the throw guard becomes a `= false` conjunct, the branches migrate out of
the monad and then inside the constructor, and `ite_self` drops the fields
an arm did not touch. What is left is one `mk` over one `ite` per guarded
field. -/

/-- A throw is an `error`, and nothing runs after it: one spelling for a
triggered guard, and no copy of what followed it. -/
@[js_norm] theorem jsm_throw_eq_error {α : Type} (e : JsError) :
    (throw e : JsM α) = .error e := rfl

@[js_norm] theorem jsm_error_bind {α β : Type} (e : JsError) (k : α → JsM β) :
    ((Except.error e : JsM α) >>= k) = .error e := rfl

/-- A guard that throws succeeds exactly when it was down and the rest
succeeded. The rest is named once, which is what keeps the fact linear. -/
@[js_norm] theorem jsm_ite_error_ok_iff {α : Type} (c : Bool) (e : JsError)
    (r : JsM α) (v : α) :
    ((if c = true then (Except.error e : JsM α) else r) = Except.ok v) ↔
      (c = false ∧ r = Except.ok v) := by
  cases c <;> simp

/-- A branch between two successes is one success over a branch. -/
@[js_norm] theorem jsm_ite_pure_pure {α : Type} (c : Bool) (a b : α) :
    (if c = true then (pure a : JsM α) else pure b) =
      pure (if c = true then a else b) := by
  cases c <;> rfl

/-- The emitted image equation spells its right-hand side `.ok`, so the
`pure`-on-both-sides injection never reaches it. -/
@[js_norm] theorem jsm_pure_eq_ok {α : Type} (a b : α) :
    ((pure a : JsM α) = Except.ok b) ↔ a = b :=
  ⟨fun h => Except.ok.inj h, fun h => h ▸ rfl⟩

-- A branch both of whose arms are one term, and a branch whose condition a
-- ground evaluator settled: neither carries information, and each collapse
-- halves the tree the closers walk.
attribute [js_norm] Bool.cond_self ite_self Bool.cond_true Bool.cond_false
  Bool.false_eq_true

-- Binary64 theory from FloatFacts. Rewriting subtraction away leaves the
-- closers one operator fewer to reason about.
attribute [js_norm, grind =] Js.Number.FloatFacts.float_sub_eq_add_neg

-- Double negation strips: reachable now that unary minus is in the
-- expression model.
attribute [js_norm, grind =] Js.Number.FloatFacts.float_neg_neg

-- Commutativity of `*` and `+`: the monotonicity facts below are keyed on
-- the right-constant orientation only; these equations let grind identify
-- the left-constant spelling with it. Grind-only — a permutative rewrite
-- has no place in a simp set.
attribute [grind =] Js.Number.FloatFacts.float_mul_comm
attribute [grind =] Js.Number.FloatFacts.float_add_comm

/-- Open bounded ∀s so the closers see the inequalities. Tagged for grind
too: the grind rung shares the normalization knowledge. -/
@[js_norm, grind =] theorem ballIco_iff (lo hi : Int) (p : Int → Prop) :
    ballIco lo hi p ↔ ∀ x : Int, lo ≤ x → x < hi → p x :=
  Iff.rfl

/-! The four monotonicity facts, restated on `floatInf` so their bound
hypotheses match what number binders emit, and given grind patterns keyed
on the operation terms: whenever both sides of a comparison goal apply
the same operation, the fact instantiates and the guard chain closes by
forward reasoning. -/

/-- Multiplying both sides by a positive finite factor. -/
theorem float_le_mul_of_le {x y c : Float} (h : Float.le x y = true)
    (h0 : (0 : Float) < c) (hInf : c < floatInf) :
    Float.le (x * c) (y * c) = true :=
  FloatFacts.float_le_mul_right h h0 hInf

/-- Adding a finite offset to both sides. -/
theorem float_le_add_of_le {x y c : Float} (h : Float.le x y = true)
    (hLo : -floatInf < c) (hHi : c < floatInf) :
    Float.le (x + c) (y + c) = true :=
  FloatFacts.float_le_add_right h hLo hHi

/-- Dividing both sides by a positive finite divisor. -/
theorem float_le_div_of_le {x y c : Float} (h : Float.le x y = true)
    (h0 : (0 : Float) < c) (hInf : c < floatInf) :
    Float.le (x / c) (y / c) = true :=
  FloatFacts.float_le_div_right h h0 hInf

/-- Bounds flip under negation: the offset the sub-rewrite negates keeps
its finiteness. -/
theorem float_neg_lo {c : Float} (h : c < floatInf) : -floatInf < -c :=
  FloatFacts.float_neg_bound_lo h

theorem float_neg_hi {c : Float} (h : -floatInf < c) : -c < floatInf :=
  FloatFacts.float_neg_bound_hi h

/-! A finite binder bound reaches the infinity hypotheses through one
ground comparison: transitivity chains `c < 1000` with `1000 < floatInf`,
and the ground link evaluates away during grind preprocessing. The
infinity endpoint is fixed in each statement so the binder-emitted
comparison alone determines the instantiation. -/

theorem float_lt_inf_of_lt {a b : Float} (h : a < b) (hb : b < floatInf) :
    a < floatInf :=
  FloatFacts.float_lt_trans h hb

theorem float_lt_inf_of_le {a b : Float} (h : a ≤ b) (hb : b < floatInf) :
    a < floatInf :=
  FloatFacts.float_lt_of_le_of_lt h hb

theorem float_gt_neg_inf_of_lt {a b : Float} (ha : -floatInf < a) (h : a < b) :
    -floatInf < b :=
  FloatFacts.float_lt_trans ha h

theorem float_gt_neg_inf_of_le {a b : Float} (ha : -floatInf < a) (h : a ≤ b) :
    -floatInf < b :=
  FloatFacts.float_lt_of_lt_of_le ha h

/-- IEEE comparison is total away from NaN, so a branch condition that came
back false is the reverse comparison. What rules NaN out is the pair of
infinity bounds a `number` binder emits; a literal operand's own pair is
ground and evaluates away. -/
theorem float_le_of_not_lt {x y : Float} (hxLo : -floatInf < x) (hxHi : x < floatInf)
    (hyLo : -floatInf < y) (hyHi : y < floatInf) (h : Float.lt x y = false) :
    Float.le y x = true :=
  FloatFacts.float_le_of_not_lt hxLo hxHi hyLo hyHi h

/-- A guard that passed refutes its own strict comparison: a constructor
surviving `0 <= a` leaves the throwing arm's `a < 0` false. -/
theorem float_lt_eq_false_of_le {x y : Float} (h : Float.le y x = true) :
    Float.lt x y = false :=
  FloatFacts.float_lt_eq_false_of_le h

/-! The non-negativity chain: square, sum, square root. The NaN bridges
are its entry points, restated on `floatInf` so the bound hypotheses a
`number` binder emits instantiate them directly. -/

/-- A float strictly inside the infinities is not NaN. -/
theorem float_ne_nan_of_bounds {c : Float} (hLo : -floatInf < c) (hHi : c < floatInf) :
    c.toModel.unpack ≠ .notANumber :=
  FloatFacts.unpack_ne_nan hLo hHi

/-- Subtraction of floats strictly inside the infinities is never NaN;
overflow to an infinity is absorbed downstream. -/
theorem float_sub_ne_nan_of_bounds {a b : Float}
    (haLo : -floatInf < a) (haHi : a < floatInf)
    (hbLo : -floatInf < b) (hbHi : b < floatInf) :
    (a - b).toModel.unpack ≠ .notANumber :=
  FloatFacts.float_sub_ne_nan haLo haHi hbLo hbHi

/-- A square is non-negative whatever the operand's sign, overflow to
`+∞` included. -/
theorem float_sq_nonneg {x : Float} (hx : x.toModel.unpack ≠ .notANumber) :
    Float.le 0 (x * x) = true :=
  FloatFacts.float_sq_nonneg hx

/-- A sum of non-negatives stays non-negative. -/
theorem float_add_nonneg {a b : Float}
    (ha : Float.le 0 a = true) (hb : Float.le 0 b = true) :
    Float.le 0 (a + b) = true :=
  FloatFacts.float_add_nonneg ha hb

/-- The square root of a non-negative float is non-negative. -/
theorem float_sqrt_nonneg {x : Float} (hx : Float.le 0 x = true) :
    Float.le 0 (Float.sqrt x) = true :=
  FloatFacts.float_sqrt_nonneg hx

/-! Guard refutation: the bounds a `number` binder emits rule out the
equality tests a throwing guard makes — IEEE equality with an infinity,
SameValue with NaN. Refuting the condition is the only way to discharge
an arm whose body is a `throw`, which no pure result equals. -/

/-- Bounded above means not `+∞`. -/
theorem float_beq_inf_eq_false {x : Float} (hHi : x < floatInf) :
    Float.beq x floatInf = false :=
  FloatFacts.float_beq_inf_eq_false hHi

/-- Bounded below means not `-∞`. -/
theorem float_beq_neg_inf_eq_false {x : Float} (hLo : -floatInf < x) :
    Float.beq x (-floatInf) = false :=
  FloatFacts.float_beq_neg_inf_eq_false hLo

/-- A float strictly inside the infinities is not SameValue-equal to NaN. -/
theorem sameValue_nan_eq_false {x : Float}
    (hLo : -floatInf < x) (hHi : x < floatInf) :
    Number.FloatOps.sameValue x floatNaN = false :=
  decide_eq_false (FloatFacts.float_ne_nan (FloatFacts.unpack_ne_nan hLo hHi))

/-! The converse direction: a constructor that survived its guards hands
the proof refuted equality tests, not bounds. These recover the strict
bounds from the refutations, which is the only finiteness a class binder
has. -/

/-- Not IEEE-equal to `+∞` (and not NaN) means strictly below it. -/
theorem float_lt_inf_of_beq_false {x : Float}
    (hn : x.toModel.unpack ≠ .notANumber)
    (h : Float.beq x floatInf = false) : x < floatInf :=
  FloatFacts.float_lt_inf_of_beq_false hn h

/-- Not IEEE-equal to `-∞` (and not NaN) means strictly above it. -/
theorem float_gt_neg_inf_of_beq_false {x : Float}
    (hn : x.toModel.unpack ≠ .notANumber)
    (h : Float.beq x (-floatInf) = false) : -floatInf < x :=
  FloatFacts.float_gt_neg_inf_of_beq_false hn h

/-- A `Number.isFinite` guard that let a value through puts it strictly
above `-∞`. -/
theorem float_lo_of_isFinite {x : Float} (h : Float.isFinite x = true) :
    -floatInf < x :=
  FloatFacts.float_lo_of_isFinite h

/-- The same guard puts it strictly below `+∞`. -/
theorem float_hi_of_isFinite {x : Float} (h : Float.isFinite x = true) :
    x < floatInf :=
  FloatFacts.float_hi_of_isFinite h

/-- Reverse direction: the strict bounds alone give finiteness back. -/
theorem isFinite_of_bounds {x : Float} (hLo : -floatInf < x) (hHi : x < floatInf) :
    Float.isFinite x = true :=
  FloatFacts.isFinite_of_bounds hLo hHi

/-- Finiteness is exactly the two strict bounds. The NaN conjunct a JS
reading would add is redundant: IEEE `<` already excludes NaN. -/
theorem isFinite_iff {x : Float} :
    Float.isFinite x = true ↔ (-floatInf < x ∧ x < floatInf) :=
  ⟨fun h => ⟨float_lo_of_isFinite h, float_hi_of_isFinite h⟩,
   fun ⟨hLo, hHi⟩ => isFinite_of_bounds hLo hHi⟩

/-! A constructor's guards throw, so what follows a triggered guard never
runs. These two are what let a successful construction refute the guards
it passed; both are definitional on `Except`, and neither is derivable
from the monad laws the closers already know. -/

/-- A throw discards its continuation. -/
@[simp, grind =] theorem jsm_throw_bind {α β : Type} (e : JsError) (k : α → JsM β) :
    (throw e >>= k) = .error e := rfl

/-- A pure result is an `ok`. -/
@[simp, grind =] theorem jsm_pure_eq {α : Type} (a : α) : (pure a : JsM α) = .ok a := rfl

/-- A refuted SameValue test against NaN means the value does not unpack
to NaN — the fact that feeds the two lemmas above. -/
theorem unpack_ne_nan_of_sameValue_false {x : Float}
    (h : Number.FloatOps.sameValue x floatNaN = false) :
    x.toModel.unpack ≠ .notANumber := by
  intro hu
  have hx : x = floatNaN := FloatFacts.float_eq_nan_of_unpack_nan hu
  simp [Number.FloatOps.sameValue, hx] at h

open Lean Meta Simp in
/-- Evaluates a closed `Float` comparison by reducing its `Decidable`
instance, the way the `decide` tactic does; the kernel recomputes the
reduction when it checks the `Eq.refl` certificate. -/
def reduceGroundFloatCmp (e : Expr) : SimpM Step := do
  if e.hasFVar || e.hasExprMVar then return .continue
  let inst ←
    try synthInstance (mkApp (mkConst ``Decidable) e)
    catch _ => return .continue
  let r ← withAtLeastTransparency .default <| whnf inst
  if r.isAppOf ``Decidable.isTrue then
    return .done { expr := mkConst ``True, proof? := some (← mkEqTrue (← mkDecideProof e)) }
  if r.isAppOf ``Decidable.isFalse then
    let decEqFalse ← mkEq (mkApp2 (mkConst ``Decidable.decide) e inst) (mkConst ``Bool.false)
    let h := mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.false)) decEqFalse
    let pf := mkApp3 (mkConst ``of_decide_eq_false) e inst h
    return .done { expr := mkConst ``False, proof? := some (← mkEqFalse pf) }
  return .continue

/-- A literal factor instantiates a monotonicity fact with ground bound
hypotheses; these evaluate away during normalization. Registered in
`seval` because that is the set both grind and the generic rung draw
their simprocs from. -/
simproc [seval] reduceFloatLt ((_ : Float) < _) := reduceGroundFloatCmp

simproc [seval] reduceFloatLe ((_ : Float) ≤ _) := reduceGroundFloatCmp

open Lean Meta Simp in
/-- The same evaluation one level down, on the `Bool` the source-level
comparisons actually lower to. A branch whose arms are literals leaves
exactly these behind once the condition has been split on. -/
def reduceGroundFloatBool (e : Expr) : SimpM Step := do
  if e.hasFVar || e.hasExprMVar then return .continue
  let r ← withAtLeastTransparency .default <| whnf e
  unless r.isConstOf ``Bool.true || r.isConstOf ``Bool.false do return .continue
  let pf ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e r)
  return .done { expr := r, proof? := some pf }

simproc [seval] reduceFloatLtBool (Float.lt _ _) := reduceGroundFloatBool

simproc [seval] reduceFloatLeBool (Float.le _ _) := reduceGroundFloatBool

simproc [seval] reduceFloatBeqBool (Float.beq _ _) := reduceGroundFloatBool

universe u v

/-- One argument's worth of pushing a branch inside an application. -/
theorem ite_app_push {α : Sort u} {β : Sort v} (c : Prop) (inst : Decidable c)
    (f g : α → β) (x y : α) :
    (@ite _ c inst (f x) (g y)) = (@ite _ c inst f g) (@ite _ c inst x y) := by
  cases inst <;> rfl

open Lean Meta Simp in
/-- A branch whose arms build the same constructor is that constructor over
branches. There is no first-order pattern for "the same constructor on both
sides", and pushing unconditionally would fire on every `ite` between two
applications, so the guard lives here rather than in a lemma. One argument
moves per step and simp revisits the head, so the arms of an inner guard
have already collapsed by the time an outer one is reached — which is what
keeps a guarded constructor's image linear in its guards. -/
simproc [js_norm] iteCtorPush (ite _ _ _) := fun e => do
  unless e.isAppOfArity ``ite 5 do return .continue
  let args := e.getAppArgs
  let a := args[3]!
  let b := args[4]!
  let .const ctorName _ := a.getAppFn | return .continue
  let .const otherName _ := b.getAppFn | return .continue
  unless ctorName == otherName do return .continue
  let some (.ctorInfo ctor) := (← getEnv).find? ctorName | return .continue
  let arity := a.getAppNumArgs
  -- Below the fields are the constructor's parameters, which the arms
  -- share: pushing those would branch over types, and `ite_self` collapses
  -- what is left anyway.
  unless arity == b.getAppNumArgs && arity > ctor.numParams do return .continue
  let some pf ← (do
      try
        return some (← mkAppOptM ``ite_app_push
          #[none, none, some args[1]!, some args[2]!,
            some a.appFn!, some b.appFn!, some a.appArg!, some b.appArg!])
      catch _ => return none)
    | return .continue
  let some (_, _, pushed) := (← inferType pf).eq? | return .continue
  return .visit { expr := pushed, proof? := some pf }

grind_pattern float_le_mul_of_le => x * c, y * c
grind_pattern float_le_add_of_le => x + c, y + c
grind_pattern float_le_div_of_le => x / c, y / c
grind_pattern float_neg_lo => -c
grind_pattern float_neg_hi => -c
grind_pattern float_lt_inf_of_lt => a < b
grind_pattern float_lt_inf_of_le => a ≤ b
grind_pattern float_gt_neg_inf_of_lt => a < b
grind_pattern float_gt_neg_inf_of_le => a ≤ b
grind_pattern float_le_of_not_lt => Float.lt x y
grind_pattern float_lt_eq_false_of_le => Float.lt x y
grind_pattern float_ne_nan_of_bounds => c.toModel.unpack
grind_pattern float_sub_ne_nan_of_bounds => (a - b).toModel.unpack
-- Normalization rewrites subtraction to addition of the negation, so the
-- residual a closer actually sees carries the second spelling.
grind_pattern float_sub_ne_nan_of_bounds => (a + -b).toModel.unpack
grind_pattern float_sq_nonneg => x * x
grind_pattern float_add_nonneg => a + b
grind_pattern float_sqrt_nonneg => Float.sqrt x
grind_pattern float_beq_inf_eq_false => Float.beq x floatInf
grind_pattern float_beq_neg_inf_eq_false => Float.beq x (-floatInf)
grind_pattern sameValue_nan_eq_false => Number.FloatOps.sameValue x floatNaN
grind_pattern float_lt_inf_of_beq_false => Float.beq x floatInf
grind_pattern float_gt_neg_inf_of_beq_false => Float.beq x (-floatInf)
grind_pattern unpack_ne_nan_of_sameValue_false => Number.FloatOps.sameValue x floatNaN
grind_pattern float_lo_of_isFinite => Float.isFinite x
grind_pattern float_hi_of_isFinite => Float.isFinite x
grind_pattern isFinite_of_bounds => Float.isFinite x

end Js
