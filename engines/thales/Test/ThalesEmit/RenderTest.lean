import Test.ThalesEmit.Support

/-! One guard per rendering rule: the tree the renderer builds against the
tree a person would write, no pretty-printer in the loop. -/

open Lean ThalesEmit

def nums (names : Array String) : Array Param :=
  names.map fun n => { name := n, ty := .number }

def v (e : JsExpr) : RenderM Rendered := valueTerm (fun _ => false) e
/-- With `x` an Int-valued binder. -/
def vx (e : JsExpr) : RenderM Rendered := valueTerm (· == "x") e
def call1 (f x : String) : JsExpr := .call f none #[.id x]

-- Literals: decimal and scientific print as themselves, the two
-- non-finite spellings as the Js library's constants, a sign as negation.
#guard rendersAs (v (.num "3")) `(3)
#guard rendersAs (v (.num "1.5")) `(1.5)
#guard rendersAs (v (.num "1e3")) `(1e3)
#guard rendersAs (v (.num "-2")) `(-2)
#guard rendersAs (v (.num "Infinity")) `(floatInf)
#guard rendersAs (v (.num "-Infinity")) `(-floatInf)
#guard rendersAs (v (.num "NaN")) `(floatNaN)

-- Identifiers: an Int binder crosses to Float at each use; a reserved
-- spelling is primed; a non-identifier is refused.
#guard rendersAs (v (.id "x")) `(x)
#guard rendersAs (vx (.id "x")) `(Float.ofInt x)
#guard rendersAs (vx (.id "y")) `(y)
#guard rendersAs (v (.id "pure")) `(pure')
#guard rendersAs (v (.id "floatNaN")) `(floatNaN')
#guard renderFails (v (.id ""))
#guard renderFails (v (.id "a-b"))

-- Unary: minus negates, plus is the identity, bang is Bool.not.
#guard rendersAs (v (.unop "-" (.id "x"))) `(-x)
#guard rendersAs (v (.unop "+" (.id "x"))) `(x)
#guard rendersAs (v (.unop "!" (.id "b"))) `(!b)
#guard renderFails (v (.unop "~" (.id "x")))

-- Arithmetic and comparison. `>`/`>=` flip into the IEEE predicates.
#guard rendersAs (v (.binop "+" (.id "x") (.id "y"))) `(x + y)
#guard rendersAs (v (.binop "-" (.id "x") (.id "y"))) `(x - y)
#guard rendersAs (v (.binop "*" (.id "x") (.id "y"))) `(x * y)
#guard rendersAs (v (.binop "/" (.id "x") (.id "y"))) `(x / y)
#guard rendersAs (v (.binop "%" (.id "x") (.id "y"))) `(Number.FloatOps.tsRem x y)
#guard rendersAs (v (.binop "<" (.id "x") (.id "y"))) `(Float.lt x y)
#guard rendersAs (v (.binop "<=" (.id "x") (.id "y"))) `(Float.le x y)
#guard rendersAs (v (.binop ">" (.id "x") (.id "y"))) `(Float.lt y x)
#guard rendersAs (v (.binop ">=" (.id "x") (.id "y"))) `(Float.le y x)
#guard rendersAs (v (.binop "===" (.id "x") (.id "y"))) `(Float.beq x y)
#guard rendersAs (v (.binop "!==" (.id "x") (.id "y"))) `(!Float.beq x y)
#guard renderFails (v (.binop "**" (.id "x") (.id "y")))
-- A flip with one lift keeps the lift where it is; with two, a lambda
-- keeps the lifts in JS evaluation order.
#guard rendersLifted (v (.binop ">" (call1 "f" "x") (.id "y"))) true
  `(Float.lt y (← TsModel.f x))
#guard rendersLifted (v (.binop ">=" (call1 "f" "x") (call1 "g" "y"))) true
  `((fun a b => Float.le b a) (← TsModel.f x) (← TsModel.g y))
#guard rendersLifted (v (.binop "+" (call1 "f" "x") (.num "1"))) true
  `((← TsModel.f x) + 1)

-- Logical: pure operands are the Bool operators; a lifted right operand
-- renders behind the choice, ascribed, so its effects never hoist.
#guard rendersLifted (v (.binop "||" (.id "a") (.id "b"))) false `(a || b)
#guard rendersLifted (v (.binop "&&" (.id "a") (.id "b"))) false `(a && b)
#guard rendersLifted (v (.binop "||" (.id "a") (call1 "f" "x"))) true
  `((← if a then pure true else ((do return (← TsModel.f x)) : JsM Bool)))
#guard rendersLifted (v (.binop "&&" (.id "a") (call1 "f" "x"))) true
  `((← if a then ((do return (← TsModel.f x)) : JsM Bool) else pure false))
#guard rendersLifted (v (.binop "||" (call1 "f" "x") (.id "b"))) true
  `((← TsModel.f x) || b)

-- SameValue, the conditional, and the builtin applications.
#guard rendersAs (v (.sameValue (.id "x") (.num "-0"))) `(Number.FloatOps.sameValue x (-0))
#guard rendersAs (vx (.sameValue (.id "x") (.num "1"))) `(Number.FloatOps.sameValue (Float.ofInt x) 1)
#guard rendersLifted (v (.cond (.id "c") (.num "0") (.id "x"))) false `(if c then 0 else x)
#guard rendersLifted (v (.cond (call1 "f" "c") (.num "0") (.id "x"))) true
  `(if (← TsModel.f c) then 0 else x)
#guard rendersLifted (v (.cond (.id "c") (call1 "f" "x") (.num "0"))) true
  `((← if c then ((do return (← TsModel.f x)) : JsM _) else ((do return 0) : JsM _)))
#guard rendersAs (v (.mathSqrt (.id "x"))) `(Float.sqrt x)
#guard rendersAs (vx (.mathSqrt (.id "x"))) `(Float.sqrt (Float.ofInt x))
#guard rendersAs (v (.mathAbs (.id "x"))) `(Float.abs x)
#guard rendersAs (v (.numberIsFinite (.id "x"))) `(Float.isFinite x)
#guard rendersAs (v (.numberIsNaN (.id "x"))) `(Float.isNaN x)

-- Calls lift, under the model namespace, a dependency's one component
-- deeper; a binder named after the callee cannot capture it.
#guard rendersLifted (v (.call "f" none #[])) true `((← TsModel.f))
#guard rendersLifted (v (.call "f" none #[.id "x", .id "y"])) true `((← TsModel.f x y))
#guard rendersLifted (v (.call "f" (some "helper.mts") #[.id "x"])) true
  `((← TsModel.«helper.mts».f x))
#guard rendersAs (v (.call "bump" none #[.id "bump"])) `((← TsModel.bump bump))
#guard rendersAs (vx (.call "f" none #[.id "x"])) `((← TsModel.f (Float.ofInt x)))
#guard renderFails (v (.call "helper.mts::double" none #[]))

-- Classes: construction, getter, field, method, receiver.
#guard rendersLifted (v (.newObj "Box" none #[.id "x"])) true `((← TsModel.Box.construct x))
#guard rendersLifted (v (.newObj "Box" none #[])) true `((← TsModel.Box.construct))
#guard rendersLifted (v (.getterRead "Box" none "v" .selfRef)) true `((← TsModel.Box.v self))
#guard rendersLifted (v (.fieldRead "Box" none "#v" .selfRef)) false `(TsModel.Box.«#v» self)
#guard rendersLifted (v (.fieldRead "Box" none "v" (.newObj "Box" none #[.id "x"]))) true
  `(TsModel.Box.v (← TsModel.Box.construct x))
#guard rendersLifted (v (.methodCall "Box" none "m" (.id "b") #[.id "k"])) true
  `((← TsModel.Box.m b k))
#guard rendersLifted (v (.methodCall "Box" none "double" (.newObj "Box" none #[.id "x"]) #[])) true
  `((← TsModel.Box.double (← TsModel.Box.construct x)))
#guard rendersAs (v .selfRef) `(self)
#guard rendersAs (v (.fieldRead "Box" (some "b.mts") "v" .selfRef)) `(TsModel.«b.mts».Box.v self)

-- Module constants read as qualified references.
#guard rendersLifted (v (.constRead "cap" none)) false `(TsModel.cap)
#guard rendersAs (v (.constRead "cap" (some "c.mts"))) `(TsModel.«c.mts».cap)

-- The tagged domain: injection by constructor, the throwing projection
-- behind a bind, typeof as a TypeofResult comparison, both equalities.
#guard rendersLifted (v (.inject .number (some (.id "x")))) false `(JsVal.num x)
#guard rendersAs (vx (.inject .number (some (.id "x")))) `(JsVal.num (Float.ofInt x))
#guard rendersAs (v (.inject .boolean (some (.id "b")))) `(JsVal.bool b)
#guard rendersAs (v (.inject .undefined none)) `(JsVal.undef)
#guard rendersAs (v (.inject .null none)) `(JsVal.null)
#guard renderFails (v (.inject .string (some (.id "s"))))
#guard renderFails (v (.inject .number none))
#guard rendersLifted (v (.project .number (.id "w"))) true `((← JsVal.toNumber w))
#guard renderFails (v (.project .string (.id "w")))
#guard rendersAs (v (.typeofTest (.id "w") "number")) `(JsVal.typeof w == TypeofResult.number)
#guard renderFails (v (.typeofTest (.id "w") "numbr"))
#guard rendersAs (v (.jsvalEq true (.id "w") (.inject .null none))) `(JsVal.sameValue w JsVal.null)
#guard rendersAs (v (.jsvalEq false (.id "w") (.id "u"))) `(JsVal.strictEq w u)

-- Options: injection, the two tests, the throwing get.
#guard rendersLifted (v (.optionInject (some (.id "q")))) false `(some q)
#guard rendersAs (v (.optionInject none)) `(none)
#guard rendersAs (v (.optionTest (.id "p") true)) `(Option.isSome p)
#guard rendersAs (v (.optionTest (.id "p") false)) `(Option.isNone p)
#guard rendersLifted (v (.optionGet (.id "p"))) true `((← Js.optionGet p))

def m (e : JsExpr) : RenderM (Term × Bool) := monadicTerm (fun _ => false) e

-- A bare call pins the monad; anything else lifts with `pure` or a
-- `do return` and pins nothing.
#guard monadicAs (m (.call "f" none #[.id "x"])) true `(TsModel.f x)
#guard monadicAs (m (.call "f" none #[call1 "g" "x"])) false
  `(do return (← TsModel.f (← TsModel.g x)))
#guard monadicAs (m (.binop "+" (call1 "f" "x") (.num "1"))) false
  `(do return (← TsModel.f x) + 1)
#guard monadicAs (m (.binop "+" (.id "x") (.num "1"))) false `(pure (x + 1))

-- A boolean island is `= pure true`, ascribed on the pure side too.
#guard rendersSyntax (boolIsland (fun _ => false) (.binop "<" (.id "x") (.num "1")))
  `((pure (Float.lt x 1) : JsM Bool) = pure true)
#guard rendersSyntax (boolIsland (fun _ => false) (.binop "<" (call1 "f" "x") (.num "1")))
  `(((do return Float.lt (← TsModel.f x) 1) : JsM Bool) = pure true)

-- The operand order of a bound hypothesis carries which side it is.
#guard rendersSyntax (do boundHyp (← `(a)) (← `(b)) .lt (← `(P))) `(a < b → P)
#guard rendersSyntax (do boundHyp (← `(a)) (← `(b)) .le (← `(P))) `(a ≤ b → P)

/-- One obligation over `f`, as the emitter sees it. -/
def obl (binders : Array BinderIR) (guards : Array JsExpr) (c : Conclusion) :
    RenderM (TSyntax `command) :=
  obligationCommand { file := "t.ts", declarations := #[], obligations := #[] }
    { function := "f", property := "p", formula := "",
      payload := .structured binders guards c }

-- The bare payload is the stub form.
#guard rendersSyntax
  (obligationCommand { file := "t.ts", declarations := #[], obligations := #[] }
    { function := "f", property := "p", formula := "", payload := .bare })
  `(#thales_prove "t.ts" "f" "p")

-- Conclusions: a pinning side leaves the equation bare; neither pinning
-- ascribes the left; a boolean island is the `= pure true` shape.
#guard rendersSyntax (obl #[.number "x" none none] #[] (.eq (call1 "f" "x") (.id "x")))
  `(#thales_prove "t.ts" "f" "p" := ∀ (x : JsNumber), TsModel.f x = pure x)
#guard rendersSyntax (obl #[.number "x" none none] #[] (.eq (.id "x") (call1 "f" "x")))
  `(#thales_prove "t.ts" "f" "p" := ∀ (x : JsNumber), pure x = TsModel.f x)
#guard rendersSyntax
  (obl #[.number "x" none none] #[]
    (.eq (.binop "+" (.id "x") (.num "1")) (.binop "+" (.num "1") (.id "x"))))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ (x : JsNumber), (pure (x + 1) : JsM JsNumber) = pure (1 + x))
#guard rendersSyntax (obl #[.number "x" none none] #[] (.istrue (.binop "<" (.id "x") (.num "1"))))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ (x : JsNumber), (pure (Float.lt x 1) : JsM Bool) = pure true)

-- Guards are hypotheses in front of the leaf, first guard outermost.
#guard rendersSyntax
  (obl #[.number "x" none none] #[.binop "<" (.num "0") (.id "x"), .binop "<" (.id "x") (.num "9")]
    (.eq (call1 "f" "x") (.id "x")))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ (x : JsNumber),
        (pure (Float.lt 0 x) : JsM Bool) = pure true →
          (pure (Float.lt x 9) : JsM Bool) = pure true → TsModel.f x = pure x)

-- Binder folds, first binder outermost. Int-valued binders coerce at
-- each use; a `number` binder never does.
#guard rendersSyntax (obl #[.range "x" 0 10] #[] (.eq (call1 "f" "x") (.id "x")))
  `(#thales_prove "t.ts" "f" "p" :=
      ballIco 0 10 fun x => TsModel.f (Float.ofInt x) = pure (Float.ofInt x))
#guard rendersSyntax (obl #[.range "x" (-5) 5] #[] (.eq (call1 "f" "x") (.id "x")))
  `(#thales_prove "t.ts" "f" "p" :=
      ballIco (-5) 5 fun x => TsModel.f (Float.ofInt x) = pure (Float.ofInt x))
#guard rendersSyntax (obl #[.range "a" 0 2, .range "b" 0 3] #[] (.eq (.id "a") (.id "b")))
  `(#thales_prove "t.ts" "f" "p" :=
      ballIco 0 2 fun a => ballIco 0 3 fun b =>
        (pure (Float.ofInt a) : JsM JsNumber) = pure (Float.ofInt b))
#guard rendersSyntax (obl #[.int "x"] #[] (.eq (call1 "f" "x") (.id "x")))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ (x : Int), TsModel.f (Float.ofInt x) = pure (Float.ofInt x))
#guard rendersSyntax (obl #[.nat "n"] #[] (.eq (call1 "f" "n") (.id "n")))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ (n : Int), 0 ≤ n → TsModel.f (Float.ofInt n) = pure (Float.ofInt n))
#guard rendersSyntax
  (obl #[.number "x" (some (.lt, "0")) (some (.lt, "Infinity"))] #[] (.eq (call1 "f" "x") (.id "x")))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ (x : JsNumber), 0 < x → x < floatInf → TsModel.f x = pure x)
#guard rendersSyntax
  (obl #[.number "y" (some (.le, "-Infinity")) none] #[] (.eq (call1 "f" "y") (.id "y")))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ (y : JsNumber), -floatInf ≤ y → TsModel.f y = pure y)
#guard rendersSyntax
  (obl #[.number "y" none (some (.le, "1"))] #[] (.eq (call1 "f" "y") (.id "y")))
  `(#thales_prove "t.ts" "f" "p" := ∀ (y : JsNumber), y ≤ 1 → TsModel.f y = pure y)
-- A reserved binder spelling is primed throughout.
#guard rendersSyntax (obl #[.int "pure"] #[] (.eq (call1 "f" "pure") (.id "pure")))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ (pure' : Int), TsModel.f (Float.ofInt pure') = pure (Float.ofInt pure'))

-- A class binder: one ungrouped ∀ per constructor argument, then the
-- instance, then the constructor-image hypothesis; a defaulted argument
-- is quantified at its type and injected at the call; nested classes
-- recurse with dotted paths.
#guard rendersSyntax
  (obl #[.cls "p" "Point" none #[.number "x" false, .number "y" false]] #[]
    (.istrue (.binop "<=" (.num "0") (.methodCall "Point" none "gap" (.id "p") #[.num "1"]))))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ («p.x» : JsNumber), ∀ («p.y» : JsNumber), ∀ (p : TsModel.Point),
        TsModel.Point.construct «p.x» «p.y» = .ok p →
          ((do return Float.le 0 (← TsModel.Point.gap p 1)) : JsM Bool) = pure true)
#guard rendersSyntax
  (obl #[.cls "p" "Point" none #[.number "x" false, .number "y" true]] #[]
    (.eq (.fieldRead "Point" none "x" (.id "p")) (.fieldRead "Point" none "x" (.id "p"))))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ («p.x» : JsNumber), ∀ («p.y» : JsNumber), ∀ (p : TsModel.Point),
        TsModel.Point.construct «p.x» (JsVal.num «p.y») = .ok p →
          (pure (TsModel.Point.x p) : JsM JsNumber) = pure (TsModel.Point.x p))
#guard rendersSyntax
  (obl #[.cls "s" "Span" none #[.cls "p" "Point" none #[.number "x" false] false]] #[]
    (.eq (.fieldRead "Span" none "w" (.id "s")) (.fieldRead "Span" none "w" (.id "s"))))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ («s.p.x» : JsNumber), ∀ («s.p» : TsModel.Point),
        TsModel.Point.construct «s.p.x» = .ok «s.p» →
          ∀ (s : TsModel.Span), TsModel.Span.construct «s.p» = .ok s →
            (pure (TsModel.Span.w s) : JsM JsNumber) = pure (TsModel.Span.w s))
#guard rendersSyntax
  (obl #[.cls "s" "Span" none #[.cls "p" "Point" none #[.number "x" false] true]] #[]
    (.eq (.fieldRead "Span" none "w" (.id "s")) (.fieldRead "Span" none "w" (.id "s"))))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ («s.p.x» : JsNumber), ∀ («s.p» : TsModel.Point),
        TsModel.Point.construct «s.p.x» = .ok «s.p» →
          ∀ (s : TsModel.Span), TsModel.Span.construct (some «s.p») = .ok s →
            (pure (TsModel.Span.w s) : JsM JsNumber) = pure (TsModel.Span.w s))
-- A binder named after the callee still renders the qualified call.
#guard rendersSyntax (obl #[.int "bump"] #[] (.eq (call1 "bump" "bump") (call1 "bump" "bump")))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ (bump : Int), TsModel.bump (Float.ofInt bump) = TsModel.bump (Float.ofInt bump))

def stmt (s : JsStmt) : RenderM (TSyntax `doElem) := stmtDoElem none s
def ctorStmt (straight : List String) (s : JsStmt) : RenderM (TSyntax `doElem) :=
  stmtDoElem (some straight) s

-- One do-element per statement; locals are ascribed.
#guard rendersSyntax (stmt (.ret (.id "x"))) `(doElem| return x)
#guard rendersSyntax (stmt (.throwErr "RangeError")) `(doElem| throw (JsError.error "RangeError"))
#guard rendersSyntax (stmt (.constDecl "y" .number (.id "x"))) `(doElem| let y : JsNumber := x)
#guard rendersSyntax (stmt (.constDecl "w" (.union #[.number, .string]) (.id "v")))
  `(doElem| let w : JsVal := v)
#guard rendersSyntax (stmt (.constDecl "p" (.cls "Pt" none) (.id "q"))) `(doElem| let p : TsModel.Pt := q)
#guard rendersSyntax (stmt (.letDecl "y" .number (.id "x"))) `(doElem| let mut y : JsNumber := x)
#guard rendersSyntax (stmt (.assign "y" (.binop "+" (.id "y") (.num "1")))) `(doElem| y := y + 1)

-- `if` chains: no else, an else, an else-if grafted onto the same node,
-- an empty arm as `pure ()`.
#guard rendersSyntax (stmt (.ite (.id "c") #[.ret (.num "0")] none))
  `(doElem| if c then return 0)
#guard rendersSyntax (stmt (.ite (.id "c") #[.ret (.num "0")] (some #[.ret (.num "1")])))
  `(doElem| if c then return 0 else return 1)
#guard rendersSyntax
  (stmt (.ite (.id "c") #[.ret (.num "0")]
    (some #[.ite (.id "d") #[.ret (.num "1")] (some #[.ret (.num "2")])])))
  `(doElem| if c then return 0 else if d then return 1 else return 2)
#guard rendersSyntax
  (stmt (.ite (.id "c") #[.ret (.num "0")] (some #[.ite (.id "d") #[.ret (.num "1")] none])))
  `(doElem| if c then return 0 else if d then return 1)
#guard rendersSyntax (stmt (.ite (.id "c") #[] none)) `(doElem| if c then pure ())

-- Field assignment renders only inside a constructor: a straight field
-- as a let, a branch-set field as a reassignment.
#guard rendersSyntax (ctorStmt ["v"] (.fieldSet "v" (.id "v")))
  `(doElem| let «this.v» : JsNumber := v)
#guard rendersSyntax (ctorStmt [] (.fieldSet "#v" (.id "v"))) `(doElem| «this.#v» := v)
#guard renderFails (stmt (.fieldSet "v" (.id "v")))

-- Parameter groups: a maximal run of one type shares a group.
#guard rendersSyntax
  (do let bs ← paramBinders #[{ name := "x", ty := .number }, { name := "y", ty := .number }]
      `(def f $bs* : Nat := 0))
  `(def f (x y : JsNumber) : Nat := 0)
#guard rendersSyntax
  (do let bs ← paramBinders
        #[{ name := "x", ty := .number }, { name := "v", ty := .union #[.number, .string] },
          { name := "p", ty := .cls "Pt" none }, { name := "q", ty := .option "Pt" none },
          { name := "y", ty := .number }]
      `(def f $bs* : Nat := 0))
  `(def f (x : JsNumber) (v : JsVal) (p : TsModel.Pt) (q : Option TsModel.Pt) (y : JsNumber) : Nat := 0)

-- A function: dual-tagged, namespaced, an assigned parameter rebound
-- ahead of the body, a parameter the body itself rebinds not rebound twice.
#guard rendersSyntax
  (fnCommand { name := "add", params := nums #["a", "b"], source := "",
               body := #[.ret (.binop "+" (.id "a") (.id "b"))] })
  `(@[js_norm, grind] def TsModel.add (a b : JsNumber) : JsM JsNumber := do
      return a + b)
#guard rendersSyntax
  (fnCommand { name := "id", params := nums #["x"], source := "", body := #[.ret (.id "x")] })
  `(@[js_norm, grind] def TsModel.id (x : JsNumber) : JsM JsNumber := do
      return x)
#guard rendersSyntax
  (fnCommand { name := "clampUp", params := nums #["x"], source := "",
               body := #[.ite (.binop "<" (.id "x") (.num "1")) #[.assign "x" (.num "1")] none,
                         .ret (.id "x")] })
  `(@[js_norm, grind] def TsModel.clampUp (x : JsNumber) : JsM JsNumber := do
      let mut x := x
      if Float.lt x 1 then x := 1
      return x)
#guard rendersSyntax
  (fnCommand { name := "f", params := #[{ name := "x", ty := .number },
                                        { name := "y", ty := .union #[.number, .undefined] }],
               source := "",
               body := #[.letDecl "y" .number
                           (.cond (.jsvalEq false (.id "y") (.inject .undefined none))
                             (.num "1") (.project .number (.id "y"))),
                         .assign "y" (.binop "+" (.id "y") (.id "x")),
                         .ret (.id "y")] })
  `(@[js_norm, grind] def TsModel.f (x : JsNumber) (y : JsVal) : JsM JsNumber := do
      let mut y : JsNumber :=
        (← if JsVal.strictEq y JsVal.undef then ((do return 1) : JsM _)
           else ((do return (← JsVal.toNumber y)) : JsM _))
      y := y + x
      return y)
#guard rendersSyntax
  (fnCommand { name := "double", module := some "helper.mts", params := nums #["x"], source := "",
               body := #[.ret (.binop "*" (.id "x") (.num "2"))] })
  `(@[js_norm, grind] def TsModel.«helper.mts».double (x : JsNumber) : JsM JsNumber := do
      return x * 2)
#guard renderFails
  (fnCommand { name := "helper.mts::double", params := nums #["x"], source := "", body := #[.ret (.id "x")] })
#guard renderFails
  (fnCommand { name := "d", module := some "a«b", params := nums #["x"], source := "", body := #[.ret (.id "x")] })
#guard renderFails
  (fnCommand { name := "d", module := some "/abs.ts", params := nums #["x"], source := "", body := #[.ret (.id "x")] })
#guard renderFails
  (fnCommand { name := "d", module := some "", params := nums #["x"], source := "", body := #[.ret (.id "x")] })

-- A constant is a pure, dual-tagged def whose body is the initializer as
-- written: a derived constant reads the earlier def, never its value.
#guard rendersSyntax (constCommand { name := "cap", init := .num "1000", source := "" })
  `(@[js_norm, grind] def TsModel.cap : JsNumber := 1000)
#guard rendersSyntax (constCommand { name := "cap", module := some "constants.mts", init := .num "-0.5", source := "" })
  `(@[js_norm, grind] def TsModel.«constants.mts».cap : JsNumber := -0.5)
#guard rendersSyntax (constCommand { name := "m", init := .binop "*" (.constRead "s" none) (.num "60"), source := "" })
  `(@[js_norm, grind] def TsModel.m : JsNumber := TsModel.s * 60)
#guard rendersSyntax (constCommand
    { name := "h", module := some "units.mts",
      init := .binop "+" (.binop "*" (.constRead "m" (some "units.mts")) (.num "60")) (.unop "-" (.constRead "s" (some "units.mts"))),
      source := "" })
  `(@[js_norm, grind] def TsModel.«units.mts».h : JsNumber := TsModel.«units.mts».m * 60 + -TsModel.«units.mts».s)
-- The frontend never emits a lift in an initializer; one arriving is a
-- contract violation, refused rather than rendered into a pure def.
#guard renderFails (constCommand { name := "bad", init := .call "f" none #[.num "1"], source := "" })

/-- A one-field class with a straight constructor. -/
def box : EmitClass :=
  { name := "Box", source := "", fields := #["#v"], ctorParams := nums #["v"],
    ctorBody := #[.fieldSet "#v" (.id "v")],
    getters := #[{ name := "v", body := #[.ret (.fieldRead "Box" none "#v" .selfRef)] }],
    methods := #[{ name := "scale", params := nums #["k"],
                   body := #[.ret (.binop "*" (.fieldRead "Box" none "#v" .selfRef) (.id "k"))] }] }

/-- A field the printer would not escape carries its guillemets inside the
name component, a spelling no quotation can write, so it is spliced. -/
def hashV : Ident := mkIdent (Name.mkSimple "«#v»")

-- Structure, constructor, getter, method.
#guard rendersSyntax (structCommand box) `(structure TsModel.Box where $hashV:ident : JsNumber)
#guard rendersSyntax (structCommand { box with fields := #[], ctorParams := #[], ctorBody := #[] })
  `(structure TsModel.Box)
#guard rendersSyntax (ctorCommand box)
  `(@[js_norm, grind] def TsModel.Box.construct (v : JsNumber) : JsM TsModel.Box := do
      let «this.#v» : JsNumber := v
      return TsModel.Box.mk «this.#v»)
-- A field set inside a branch gets the mut prelude.
#guard rendersSyntax
  (ctorCommand { box with
                 fields := #["v"],
                 ctorBody := #[.ite (.binop "<" (.id "v") (.num "0"))
                                 #[.fieldSet "v" (.num "0")] (some #[.fieldSet "v" (.id "v")])] })
  `(@[js_norm, grind] def TsModel.Box.construct (v : JsNumber) : JsM TsModel.Box := do
      let mut «this.v» : JsNumber := 0
      if Float.lt v 0 then «this.v» := 0 else «this.v» := v
      return TsModel.Box.mk «this.v»)
#guard rendersSyntax (getterCommand box box.getters[0]!)
  `(@[js_norm, grind] def TsModel.Box.v (self : TsModel.Box) : JsM JsNumber := do
      return TsModel.Box.«#v» self)
#guard rendersSyntax (methodCommand box box.methods[0]!)
  `(@[js_norm, grind] def TsModel.Box.scale (self : TsModel.Box) (k : JsNumber) : JsM JsNumber := do
      return TsModel.Box.«#v» self * k)

-- What the lift barrier buys, written out by hand: the arm the condition
-- passed over does not run, so its throw does not escape.
section
open Js
private def boom : JsM JsNumber := JsM.throw (JsError.error "E")

private def barrier (c : Bool) : JsM JsNumber := do
  return (← if c then ((do return 1) : JsM _) else ((do return (← boom)) : JsM _))

#guard (barrier true) matches .ok _
#guard (barrier false) matches .error _
end
