import Init.Data.Float.Model.Float

/-!
Background theory about binary64 arithmetic, proven from `Float.Model`.

Lean's float model ships essentially no lemmas: the ordering theory,
rounding characterization, and pack/unpack round-trips that `prove`
verdicts need all live here. Everything is kernel-checked; no axioms,
no `native_decide`.
-/

namespace ThalesDsl.FloatFacts

open Float.Model Float.Model.UnpackedFloat

/-! ## Sign algebra -/

theorem sign_apply_neg (s : Sign) (n : Int) : (-s).apply n = -(s.apply n) := by
  cases s
  · exact (Int.neg_neg n).symm
  · rfl

theorem sign_neg_neg (s : Sign) : - -s = s := by
  cases s <;> rfl

theorem sign_beq_neg_neg (s t : Sign) : (s == - -t) = (s == t) := by
  cases s <;> cases t <;> rfl

/-! ## Negation and subtraction -/

theorem neg_neg (a : UnpackedFloat) : a.neg.neg = a := by
  cases a <;> grind [UnpackedFloat.neg, sign_neg_neg]

/-- IEEE subtraction is addition of the negation, so ordering facts about
`add` transfer to `sub` without a second rounding analysis. -/
theorem sub_eq_add_neg (spec : Format) (a b : UnpackedFloat) :
    UnpackedFloat.sub spec a b = UnpackedFloat.add spec a b.neg := by
  cases a <;> cases b <;>
    grind [UnpackedFloat.sub, UnpackedFloat.add, UnpackedFloat.neg,
           sign_apply_neg, sign_neg_neg, sign_beq_neg_neg]

/-! ## Round-to-nearest-even on mantissas -/

/-- Accuracies ordered by where the discarded fraction sits relative to a
half ulp: exact, below half, exactly half, above half. -/
def accuracyRank : Accuracy → Nat
  | .exact => 0
  | .inexact .lt => 1
  | .inexact .eq => 2
  | .inexact .gt => 3

/-- Rounding respects the lexicographic order on (mantissa, discarded
fraction); this is the single-step core of every monotonicity result. -/
theorem roundToNearestEven_le_of_lex {m₁ m₂ : Nat} {a₁ a₂ : Accuracy}
    (h : m₁ < m₂ ∨ (m₁ = m₂ ∧ accuracyRank a₁ ≤ accuracyRank a₂)) :
    Accuracy.roundToNearestEven m₁ a₁ ≤ Accuracy.roundToNearestEven m₂ a₂ := by
  cases a₁ <;> cases a₂ <;>
  · first
    | grind [Accuracy.roundToNearestEven, accuracyRank]
    | (rename_i o₁ o₂
       cases o₁ <;> cases o₂ <;> grind [Accuracy.roundToNearestEven, accuracyRank])
    | (rename_i o
       cases o <;> grind [Accuracy.roundToNearestEven, accuracyRank])

/-! ## The shift pipeline as division

`roundWithAccuracy` iterates `shiftRightOne`, accumulating the discarded
bits into a round bit and a sticky bit. The closed form below replaces
that iteration with `/` and `%`, which is what the arithmetic lemmas
downstream actually consume. -/

/-- What `n` right-shifts of an exact mantissa `m` produce: the quotient,
the last bit shifted out, and whether anything below it was nonzero. -/
def shiftedForm (m n : Nat) : ExtendedMantissa :=
  if n = 0 then ⟨m, false, false⟩
  else ⟨m / 2 ^ n, m / 2 ^ (n - 1) % 2 == 1, m % 2 ^ (n - 1) != 0⟩

theorem repeat_shiftRightOne_eq (m n : Nat) :
    Nat.repeat ExtendedMantissa.shiftRightOne n ⟨m, false, false⟩ = shiftedForm m n := by
  induction n with
  | zero => simp [shiftedForm, Nat.repeat]
  | succ k ih =>
    rw [Nat.repeat, ih]
    cases k with
    | zero =>
      simp [shiftedForm, ExtendedMantissa.shiftRightOne]
      grind
    | succ j =>
      simp only [shiftedForm, ExtendedMantissa.shiftRightOne, if_neg (by omega : ¬j + 1 = 0),
        if_neg (by omega : ¬j + 1 + 1 = 0)]
      refine ExtendedMantissa.mk.injEq .. ▸ ⟨?_, ?_, ?_⟩
      · show m / 2 ^ (j + 1) / 2 = m / 2 ^ (j + 1 + 1)
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      · show (m / 2 ^ (j + 1) % 2 != 0) = (m / 2 ^ (j + 1 + 1 - 1) % 2 == 1)
        grind
      · show ((m / 2 ^ j % 2 == 1) || (m % 2 ^ j != 0)) = (m % 2 ^ (j + 1 + 1 - 1) != 0)
        have h : m % 2 ^ (j + 1) = 2 ^ j * (m / 2 ^ j % 2) + m % 2 ^ j := by
          rw [Nat.pow_succ, Nat.mod_mul]
          omega
        grind

/-- Round-to-nearest-even of `m / 2^n`, as pure arithmetic. -/
def rnShift (m n : Nat) : Nat :=
  let q := m / 2 ^ n
  let r := m % 2 ^ n
  if r * 2 < 2 ^ n then q
  else if r * 2 = 2 ^ n then q + q % 2
  else q + 1

/-- The shift pipeline's rounded mantissa is exactly `rnShift`. -/
theorem roundedMantissa_shiftedForm (m n : Nat) :
    (shiftedForm m n).roundedMantissa = rnShift m n := by
  cases n with
  | zero =>
    simp [shiftedForm, rnShift, ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven]
    grind
  | succ k =>
    have h : m % 2 ^ (k + 1) = 2 ^ k * (m / 2 ^ k % 2) + m % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mod_mul]; omega
    have hk : 0 < 2 ^ k := Nat.two_pow_pos k
    have hmk : m % 2 ^ k < 2 ^ k := Nat.mod_lt _ hk
    simp only [shiftedForm, if_neg (by omega : ¬k + 1 = 0), Nat.add_sub_cancel]
    rw [ExtendedMantissa.roundedMantissa]
    have h2' : m / 2 ^ k % 2 = 0 ∨ m / 2 ^ k % 2 = 1 := by omega
    rcases h2' with h2 | h2 <;>
      rcases Nat.eq_zero_or_pos (m % 2 ^ k) with h3 | h3 <;>
        simp [ExtendedMantissa.accuracy, h2, h3, Accuracy.roundToNearestEven,
          rnShift, Nat.pow_succ] <;> grind

theorem rnShift_mono {m m' : Nat} (n : Nat) (h : m ≤ m') : rnShift m n ≤ rnShift m' n := by
  have hq : m / 2 ^ n ≤ m' / 2 ^ n := Nat.div_le_div_right h
  have hd : 0 < 2 ^ n := Nat.two_pow_pos n
  have e1 := Nat.div_add_mod m (2 ^ n)
  have e2 := Nat.div_add_mod m' (2 ^ n)
  have r1 : m % 2 ^ n < 2 ^ n := Nat.mod_lt _ hd
  have r2 : m' % 2 ^ n < 2 ^ n := Nat.mod_lt _ hd
  rw [rnShift, rnShift]
  by_cases hqq : m / 2 ^ n = m' / 2 ^ n
  · have hr : m % 2 ^ n ≤ m' % 2 ^ n := by
      have := hqq ▸ e1; omega
    grind
  · have : m / 2 ^ n + 1 ≤ m' / 2 ^ n := by omega
    grind

/-- `rnShift` rounds the quotient to itself or its successor. -/
theorem rnShift_bounds (m n : Nat) :
    m / 2 ^ n ≤ rnShift m n ∧ rnShift m n ≤ m / 2 ^ n + 1 := by
  rw [rnShift]; grind

/-! ## Value-monotonicity of rounding

`rnPos p F m` is the value (relative to the input exponent) of `m`
rounded to `p` significant bits, but never at a granularity finer than
shift `F`; `p = 53` and `F` derived from the minimum exponent gives
binary64 rounding with subnormals. Monotonicity must cover arguments
that round at different shifts — the cross-binade case. -/

def rnPos (p F m : Nat) : Nat :=
  let n := max (m.log2 + 1 - p) F
  rnShift m n * 2 ^ n

theorem rnPos_mono_aux (p F m m' n n' : Nat) (hp : 1 ≤ p) (hm : 0 < m) (h : m ≤ m')
    (hn : n = max (m.log2 + 1 - p) F) (hn' : n' = max (m'.log2 + 1 - p) F) :
    rnShift m n * 2 ^ n ≤ rnShift m' n' * 2 ^ n' := by
  have hm' : 0 < m' := Nat.lt_of_lt_of_le hm h
  have hlog : m.log2 ≤ m'.log2 :=
    (Nat.le_log2 (by omega)).mpr (Nat.le_trans (Nat.log2_self_le (by omega)) h)
  have hnn' : n ≤ n' := by omega
  rcases Nat.eq_or_lt_of_le hnn' with heq | hlt
  · -- same shift: mantissa monotonicity
    rw [← heq]
    exact Nat.mul_le_mul_right _ (rnShift_mono n h)
  · -- n < n' forces n' into the log2 branch, so m' sits in a strictly
    -- higher binade; chain through the binade boundary 2^(m'.log2)
    have hn'val : n' = m'.log2 + 1 - p := by omega
    have hlog2' : p ≤ m'.log2 + 1 := by omega
    have hn'le : n' ≤ m'.log2 := by omega
    have hmlt : m < 2 ^ (n + p) := by
      have h1 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
      have h2 : m.log2 + 1 ≤ n + p := by omega
      exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) h2)
    have hdiv : m / 2 ^ n < 2 ^ p := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)]
      calc m < 2 ^ (n + p) := hmlt
        _ = 2 ^ p * 2 ^ n := by rw [← Nat.pow_add, Nat.add_comm]
    have hub : rnShift m n * 2 ^ n ≤ 2 ^ (p + n) := by
      have h1 : rnShift m n ≤ m / 2 ^ n + 1 := (rnShift_bounds m n).2
      have h2 : rnShift m n ≤ 2 ^ p := by omega
      calc rnShift m n * 2 ^ n ≤ 2 ^ p * 2 ^ n := Nat.mul_le_mul_right _ h2
        _ = 2 ^ (p + n) := by rw [Nat.pow_add]
    have hlb : 2 ^ m'.log2 ≤ rnShift m' n' * 2 ^ n' := by
      have h1 : 2 ^ m'.log2 ≤ m' := Nat.log2_self_le (by omega)
      have h2 : 2 ^ (m'.log2 - n') ≤ m' / 2 ^ n' := by
        rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos n')]
        calc 2 ^ (m'.log2 - n') * 2 ^ n' = 2 ^ m'.log2 := by
              rw [← Nat.pow_add]; congr 1; omega
          _ ≤ m' := h1
      have h3 : 2 ^ (m'.log2 - n') ≤ rnShift m' n' :=
        Nat.le_trans h2 (rnShift_bounds m' n').1
      calc 2 ^ m'.log2 = 2 ^ (m'.log2 - n') * 2 ^ n' := by
            rw [← Nat.pow_add]; congr 1; omega
        _ ≤ rnShift m' n' * 2 ^ n' := Nat.mul_le_mul_right _ h3
    have hmid : p + n ≤ m'.log2 := by omega
    exact Nat.le_trans hub (Nat.le_trans (Nat.pow_le_pow_right (by omega) hmid) hlb)

theorem rnPos_mono (p F : Nat) (hp : 1 ≤ p) {m m' : Nat} (h : m ≤ m') :
    rnPos p F m ≤ rnPos p F m' := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : ∀ n, rnShift 0 n = 0 := by
      intro n; rw [rnShift]; simp [Nat.two_pow_pos]
    simp [rnPos, h0]
  · exact rnPos_mono_aux p F m m' _ _ hp hm h rfl rfl

/-! ## Packing round-trips

`Float.Model` operations unpack, compute, and repack; relating two
operation results therefore always crosses `pack` followed by `unpack`.
Core ships extraction lemmas for the mantissa and exponent fields but
not the sign, so that one is here too. -/

theorem unpackSign_packComponents64 {sign : Sign} {ev : BitVec 11} {mv : BitVec 52} :
    Sign.ofBitVec (unpackSign (packComponents .binary64 sign ev mv)) = sign := by
  simp only [unpackSign, packComponents, BitVec.extractLsb]
  rw [BitVec.extractLsb'_append_eq_of_le (by omega),
    BitVec.extractLsb'_append_eq_of_le (by omega)]
  cases sign <;> rfl

/-- A normal binary64 float survives the pack/unpack round-trip. The
bounds are the canonical-form invariants for normal numbers. -/
theorem unpack_pack_of_normal64 (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (hlo : 2 ^ 52 ≤ m) (hhi : m < 2 ^ 53)
    (helo : -1074 ≤ e) (hehi : e ≤ 971) :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 (.finite s m e hm)) =
      .finite s m e hm := by
  have hlog : m.log2 = 52 := by
    have h1 : 52 ≤ m.log2 := (Nat.le_log2 (by omega)).mpr hlo
    have h2 : ¬53 ≤ m.log2 := fun hc => by
      have := (Nat.le_log2 (by omega)).mp hc; omega
    omega
  have hbias : (e + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat
      = (e + 1075).toNat := by
    show (e + (2 ^ (11 - 1) - 1 : Nat) + (52 : Nat)).toNat = (e + 1075).toNat
    omega
  rw [UnpackedFloat.pack]
  simp only [hlog, hbias]
  rw [if_neg (by omega), if_pos (by simp [Format.mantissaBits])]
  rw [UnpackedFloat.unpack]
  simp only [unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_packComponents64]
  have hne1 : BitVec.ofNat 11 (e + 1075).toNat ≠ -1#11 := by
    intro heq
    have := congrArg BitVec.toNat heq
    simp [BitVec.toNat_ofNat] at this
    omega
  have hne0 : BitVec.ofNat 11 (e + 1075).toNat ≠ 0#11 := by
    intro heq
    have := congrArg BitVec.toNat heq
    simp [BitVec.toNat_ofNat] at this
    omega
  rw [if_neg hne1, if_neg hne0]
  have hmant : (1#1 ++ BitVec.ofNat 52 m).toNat = m := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.ofNat 52 m).isLt,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp [BitVec.toNat_ofNat]
    omega
  have hb1023 : ((Format.binary64.exponentBias : Nat) : Int) = 1023 := rfl
  simp [hmant, BitVec.toNat_ofNat, hb1023]
  omega

-- Kernel-computed round-trip pins for the shapes the general lemmas do
-- not yet cover: subnormal, overflow to infinity, zero, infinity.
example :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64
      (.finite .positive 1 (-1074) (by omega))) = .finite .positive 1 (-1074) (by omega) := rfl
example :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64
      (.finite .positive (2 ^ 52) 1000 (by omega))) = .infinity .positive := rfl
example :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 (.zero .negative)) =
      .zero .negative := rfl
example :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 (.infinity .negative)) =
      .infinity .negative := rfl

end ThalesDsl.FloatFacts
