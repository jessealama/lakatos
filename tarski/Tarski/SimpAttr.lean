import Lean

/-! The registration of the evaluator's simp set.

A registered simp attribute is only usable in modules that import its
registration, so the set lives one module below its lemmas, exactly as
`Js/NormAttr.lean` does for `js_norm`. -/

/-- The evaluator's partial-evaluation set: every equation a closed,
loop-free run reduces by, and nothing that recurses on the heap or on a
loop. `Tarski/Simp.lean` fills it and says what decides membership. -/
register_simp_attr tarski_eval
