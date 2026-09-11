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

-- The boolean literals are Lean's, pure.
#guard rendersAs (v (.bool true)) `(true)
#guard rendersAs (v (.bool false)) `(false)
#guard rendersLifted (v (.bool true)) false `(true)

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
-- Builtin member calls render through the (object, member) table; an
-- Int binder still crosses to Float at the argument; an unknown pair or
-- a wrong argument count is a render failure, never a verdict.
def b1 (object member x : String) : JsExpr := .builtin object member #[.id x]
#guard rendersAs (v (b1 "Math" "sqrt" "x")) `(Float.sqrt x)
#guard rendersAs (vx (b1 "Math" "sqrt" "x")) `(Float.sqrt (Float.ofInt x))
#guard rendersAs (v (b1 "Math" "abs" "x")) `(Float.abs x)
#guard rendersAs (v (b1 "Math" "trunc" "x")) `(Number.FloatOps.tsTrunc x)
#guard rendersAs (v (b1 "Math" "floor" "x")) `(Number.FloatOps.tsFloor x)
#guard rendersAs (v (b1 "Math" "ceil" "x")) `(Number.FloatOps.tsCeil x)
#guard rendersAs (v (b1 "Math" "round" "x")) `(Number.FloatOps.tsRound x)
#guard rendersAs (v (b1 "Math" "sign" "x")) `(Number.FloatOps.tsSign x)
#guard rendersAs (v (b1 "Math" "fround" "x")) `(Number.FloatOps.tsFround x)
#guard rendersAs (v (b1 "Number" "isFinite" "x")) `(Float.isFinite x)
#guard rendersAs (v (b1 "Number" "isNaN" "x")) `(Float.isNaN x)
#guard rendersAs (v (b1 "Number" "isInteger" "x"))
  `(Number.FloatOps.tsIsInteger x)
#guard rendersAs (v (b1 "Number" "isSafeInteger" "x"))
  `(Number.FloatOps.tsIsSafeInteger x)
#guard renderFails (v (b1 "Math" "log" "x"))
#guard renderFails (v (.builtin "Math" "trunc" #[.id "x", .id "y"]))

-- The variadic members fold at the call site's arity: the identity for
-- the empty call, the argument itself for one, and a right-nested chain
-- beyond. The nesting direction is unobservable — both models are
-- associative — so it is pinned here rather than left to drift.
#guard rendersAs (v (.builtin "Math" "min" #[])) `(floatInf)
#guard rendersAs (v (.builtin "Math" "max" #[])) `(-floatInf)
#guard rendersAs (v (.builtin "Math" "min" #[.id "x"])) `(x)
#guard rendersAs (v (.builtin "Math" "max" #[.id "x"])) `(x)
#guard rendersAs (v (.builtin "Math" "min" #[.id "x", .id "y"]))
  `(Number.FloatOps.tsMin x y)
#guard rendersAs (v (.builtin "Math" "max" #[.id "x", .id "y"]))
  `(Number.FloatOps.tsMax x y)
#guard rendersAs (v (.builtin "Math" "min" #[.id "x", .id "y", .id "z"]))
  `(Number.FloatOps.tsMin x (Number.FloatOps.tsMin y z))
#guard rendersAs (v (.builtin "Math" "max" #[.id "x", .id "y", .id "z"]))
  `(Number.FloatOps.tsMax x (Number.FloatOps.tsMax y z))
#guard rendersAs (vx (.builtin "Math" "min" #[.id "x", .num "1"]))
  `(Number.FloatOps.tsMin (Float.ofInt x) 1)
-- A lift among the arguments hoists in JS evaluation order.
#guard rendersLifted (v (.builtin "Math" "max" #[.id "x", call1 "f" "y"])) true
  `(Number.FloatOps.tsMax x (← TsModel.f y))
-- The clamp shape: a fold nested inside another member's argument.
#guard rendersAs
    (v (.builtin "Math" "min" #[.builtin "Math" "max" #[.id "x", .id "lo"], .id "hi"]))
  `(Number.FloatOps.tsMin (Number.FloatOps.tsMax x lo) hi)
-- Builtin member reads render as the library's constants under the
-- source spelling; a call member or an unknown pair is a render failure.
#guard rendersAs (v (.builtinRead "Number" "EPSILON")) `(Number.EPSILON)
#guard rendersAs (v (.builtinRead "Number" "MAX_SAFE_INTEGER"))
  `(Number.MAX_SAFE_INTEGER)
#guard rendersAs (v (.builtinRead "Number" "NaN")) `(Number.NaN)
#guard rendersAs (v (.builtinRead "Math" "PI")) `(Math.PI)
#guard rendersAs (v (.unop "-" (.builtinRead "Number" "EPSILON"))) `(-Number.EPSILON)
#guard rendersLifted (v (.binop "*" (.id "x") (.builtinRead "Number" "EPSILON"))) false
  `(x * Number.EPSILON)
#guard renderFails (v (.builtinRead "Math" "TAU"))
#guard renderFails (v (.builtinRead "Math" "sqrt"))
-- `Math` joins the reserved vocabulary, like `Number`.
#guard rendersAs (v (.id "Math")) `(Math')

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
#guard rendersLifted (v (.project .boolean (.id "w"))) true `((← JsVal.toBoolean w))
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
-- A boolean binder: one ungrouped ∀ at Bool, the only spelling propSpine
-- recovers; never coerced.
#guard rendersSyntax (obl #[.range "n" 0 3, .bool "b"] #[]
    (.istrue (.binop ">=" (.call "pick" none #[.id "n", .id "b"]) (.num "0"))))
  `(#thales_prove "t.ts" "f" "p" :=
      ballIco 0 3 fun n => ∀ (b : Bool),
        ((do return Float.le 0 (← TsModel.pick (Float.ofInt n) b)) : JsM Bool) = pure true)
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
-- A boolean constructor argument heads the spine at Bool; a defaulted
-- one is injected at the boolean tag.
#guard rendersSyntax
  (obl #[.cls "f" "Flag" none #[.bool "on" false]] #[]
    (.istrue (.binop "<=" (.num "0") (.methodCall "Flag" none "level" (.id "f") #[]))))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ («f.on» : Bool), ∀ (f : TsModel.Flag),
        TsModel.Flag.construct «f.on» = .ok f →
          ((do return Float.le 0 (← TsModel.Flag.level f)) : JsM Bool) = pure true)
#guard rendersSyntax
  (obl #[.cls "f" "Flag" none #[.bool "on" true]] #[]
    (.istrue (.binop "<=" (.num "0") (.methodCall "Flag" none "level" (.id "f") #[]))))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ («f.on» : Bool), ∀ (f : TsModel.Flag),
        TsModel.Flag.construct (JsVal.bool «f.on») = .ok f →
          ((do return Float.le 0 (← TsModel.Flag.level f)) : JsM Bool) = pure true)
-- A binder named after the callee still renders the qualified call.
#guard rendersSyntax (obl #[.int "bump"] #[] (.eq (call1 "bump" "bump") (call1 "bump" "bump")))
  `(#thales_prove "t.ts" "f" "p" :=
      ∀ (bump : Int), TsModel.bump (Float.ofInt bump) = TsModel.bump (Float.ofInt bump))

def stmt (s : JsStmt) : RenderM (TSyntax `doElem) := stmtDoElem none s
def ctorStmt (straight : List (String × BindingTy)) (s : JsStmt) :
    RenderM (TSyntax `doElem) :=
  stmtDoElem (some straight) s

-- One do-element per statement; locals are ascribed.
#guard rendersSyntax (stmt (.ret (.id "x"))) `(doElem| return x)
#guard rendersSyntax (stmt (.throwErr "RangeError")) `(doElem| throw (JsError.error "RangeError"))
#guard rendersSyntax (stmt (.constDecl "y" .number (.id "x"))) `(doElem| let y : JsNumber := x)
#guard rendersSyntax (stmt (.constDecl "w" (.union #[.number, .string]) (.id "v")))
  `(doElem| let w : JsVal := v)
#guard rendersSyntax (stmt (.constDecl "p" (.cls "Pt" none) (.id "q"))) `(doElem| let p : TsModel.Pt := q)
#guard rendersSyntax (stmt (.letDecl "y" .number (.id "x"))) `(doElem| let mut y : JsNumber := x)
#guard rendersSyntax (stmt (.constDecl "b" .bool (.binop "<" (.id "n") (.num "5"))))
  `(doElem| let b : Bool := Float.lt n 5)
#guard rendersSyntax (stmt (.letDecl "found" .bool (.bool false))) `(doElem| let mut found : Bool := false)
#guard rendersSyntax (stmt (.assign "found" (.bool true))) `(doElem| found := true)
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
#guard rendersSyntax (ctorStmt [("v", .number)] (.fieldSet "v" (.id "v")))
  `(doElem| let «this.v» : JsNumber := v)
#guard rendersSyntax (ctorStmt [] (.fieldSet "#v" (.id "v"))) `(doElem| «this.#v» := v)
-- A union or class field is ascribed at its type.
#guard rendersSyntax
  (ctorStmt [("x", .union #[.number, .undefined])]
    (.fieldSet "x" (.inject .number (some (.id "v")))))
  `(doElem| let «this.x» : JsVal := JsVal.num v)
#guard rendersSyntax (ctorStmt [("inner", .cls "Inner" none)] (.fieldSet "inner" (.id "i")))
  `(doElem| let «this.inner» : TsModel.Inner := i)
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
#guard rendersSyntax
  (do let bs ← paramBinders #[{ name := "n", ty := .number }, { name := "b", ty := .bool }]
      `(def f $bs* : Nat := 0))
  `(def f (n : JsNumber) (b : Bool) : Nat := 0)

-- A function: dual-tagged, namespaced, an assigned parameter rebound
-- ahead of the body, a parameter the body itself rebinds not rebound twice.
#guard rendersSyntax
  (fnCommand { name := "add", params := nums #["a", "b"], source := "",
               body := #[.ret (.binop "+" (.id "a") (.id "b"))] })
  `(@[js_norm, grind] def TsModel.add (a b : JsNumber) : JsM JsNumber := do
      return a + b)
-- A boolean-returning function is ascribed at Bool.
#guard rendersSyntax
  (fnCommand { name := "isSmall", params := nums #["n"], source := "", returns := .bool,
               body := #[.ret (.binop "<" (.id "n") (.num "5"))] })
  `(@[js_norm, grind] def TsModel.isSmall (n : JsNumber) : JsM Bool := do
      return Float.lt n 5)
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
  { name := "Box", source := "", fields := #[{ name := "#v", ty := .number }], ctorParams := nums #["v"],
    ctorBody := #[.fieldSet "#v" (.id "v")],
    getters := #[{ name := "v", body := #[.ret (.fieldRead "Box" none "#v" .selfRef)] }],
    methods := #[{ name := "scale", params := nums #["k"],
                   body := #[.ret (.binop "*" (.fieldRead "Box" none "#v" .selfRef) (.id "k"))] }] }

/-- A field the printer would not escape carries its guillemets inside the
name component, a spelling no quotation can write, so it is spliced. -/
def hashV : Ident := mkIdent (Name.mkSimple "«#v»")

-- Structure, constructor, getter, method.
#guard rendersSyntax (structCommand box)
  `(structure TsModel.Box where $hashV:ident : JsNumber deriving Inhabited)
#guard rendersSyntax (structCommand { box with fields := #[], ctorParams := #[], ctorBody := #[] })
  `(structure TsModel.Box deriving Inhabited)
#guard rendersSyntax (ctorCommand box)
  `(@[js_norm, grind] def TsModel.Box.construct (v : JsNumber) : JsM TsModel.Box := do
      let «this.#v» : JsNumber := v
      return TsModel.Box.mk «this.#v»)
-- A field set inside a branch gets the mut prelude.
#guard rendersSyntax
  (ctorCommand { box with
                 fields := #[{ name := "v", ty := .number }],
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
-- A boolean-returning getter is ascribed at Bool, like its method shape.
#guard rendersSyntax
  (getterCommand box { name := "live", returns := .bool,
                       body := #[.ret (.binop ">" (.fieldRead "Box" none "#v" .selfRef) (.num "0"))] })
  `(@[js_norm, grind] def TsModel.Box.live (self : TsModel.Box) : JsM Bool := do
      return Float.lt 0 (TsModel.Box.«#v» self))

/-- A class over a union field and a class field. -/
def outer : EmitClass :=
  { name := "Outer", source := "",
    fields := #[{ name := "x", ty := .union #[.number, .undefined] },
                { name := "inner", ty := .cls "Inner" none }],
    ctorParams := #[{ name := "v", ty := .number }, { name := "i", ty := .cls "Inner" none }],
    ctorBody := #[.ite (.binop "<" (.id "v") (.num "0"))
                    #[.fieldSet "x" (.inject .undefined none)]
                    (some #[.fieldSet "x" (.inject .number (some (.id "v")))]),
                  .fieldSet "inner" (.id "i")],
    getters := #[], methods := #[] }

#guard rendersSyntax (structCommand outer)
  `(structure TsModel.Outer where
      x : JsVal
      inner : TsModel.Inner
      deriving Inhabited)
-- A branch-set union or class field's prelude is `default`; a number's stays `0`.
#guard rendersSyntax (ctorCommand outer)
  `(@[js_norm, grind] def TsModel.Outer.construct (v : JsNumber) (i : TsModel.Inner) :
      JsM TsModel.Outer := do
      let mut «this.x» : JsVal := default
      if Float.lt v 0 then «this.x» := JsVal.undef else «this.x» := JsVal.num v
      let «this.inner» : TsModel.Inner := i
      return TsModel.Outer.mk «this.x» «this.inner»)

/-- A class over a boolean field set from a boolean constructor parameter. -/
def flag : EmitClass :=
  { name := "Flag", source := "",
    fields := #[{ name := "on", ty := .bool }],
    ctorParams := #[{ name := "on", ty := .bool }],
    ctorBody := #[.fieldSet "on" (.id "on")],
    getters := #[], methods := #[] }

#guard rendersSyntax (structCommand flag)
  `(structure TsModel.Flag where
      on : Bool
      deriving Inhabited)
#guard rendersSyntax (ctorCommand flag)
  `(@[js_norm, grind] def TsModel.Flag.construct (on : Bool) : JsM TsModel.Flag := do
      let «this.on» : Bool := on
      return TsModel.Flag.mk «this.on»)

/-- A boolean field assigned on both arms of a branch takes the `default` prelude. -/
def toggle : EmitClass :=
  { name := "Toggle", source := "",
    fields := #[{ name := "on", ty := .bool }],
    ctorParams := #[{ name := "n", ty := .number }],
    ctorBody := #[.ite (.binop "<" (.id "n") (.num "0"))
                    #[.fieldSet "on" (.bool false)]
                    (some #[.fieldSet "on" (.bool true)])],
    getters := #[], methods := #[] }

#guard rendersSyntax (ctorCommand toggle)
  `(@[js_norm, grind] def TsModel.Toggle.construct (n : JsNumber) : JsM TsModel.Toggle := do
      let mut «this.on» : Bool := default
      if Float.lt n 0 then «this.on» := false else «this.on» := true
      return TsModel.Toggle.mk «this.on»)

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

-- A residual applies its opaque to the in-scope variables as a lift; the
-- receiver renders as `self`, an ordinary variable as itself.
#guard rendersLifted (v (.residual "f" none 1 #[.id "x", .id "y"])) true
  `((← TsModel.f.residual_1 x y))
#guard rendersLifted (v (.residual "C#m" none 2 #[.selfRef, .id "x"])) true
  `((← TsModel.C.m.residual_2 self x))
#guard rendersLifted (v (.residual "C#constructor" none 1 #[.id "a"])) true
  `((← TsModel.C.construct.residual_1 a))
#guard rendersLifted (v (.residual "f" (some "helper.mts") 1 #[])) true
  `((← TsModel.«helper.mts».f.residual_1))
#guard renderFails (v (.residual "C.m" none 1 #[]))
#guard renderFails (v (.residual "f" none 0 #[]))

-- The opaque a site declares: docstringed, noncomputable, a pi type over
-- the in-scope variables into JsM.
#guard rendersSyntax (residualCommand
    { owner := "f", site := 1, construct := "'Math.log' is not supported",
      params := #[{ name := "n", ty := .number }], ty := .number })
  `(/-- 'Math.log' is not supported -/
    noncomputable opaque TsModel.f.residual_1 : (n : JsNumber) → JsM JsNumber)
#guard rendersSyntax (residualCommand
    { owner := "C#m", site := 1, construct := "'**' is not supported",
      params := #[{ name := "self", ty := .cls "C" none }, { name := "b", ty := .bool }],
      ty := .bool })
  -- A pi binder is primed like any other, so a parameter spelled like the
  -- artifact's own vocabulary cannot capture a later type.
  `(/-- '**' is not supported -/
    noncomputable opaque TsModel.C.m.residual_1 :
      (self' : TsModel.C) → (b : Bool) → JsM Bool)
#guard renderFails (residualCommand
    { owner := "f", site := 1, construct := "closes -/ early",
      params := #[], ty := .number })

-- A tainted owner is a noncomputable def; an untainted one is unchanged.
#guard rendersSyntax (fnCommand
    { name := "f", params := nums #["x"], source := "", tainted := true,
      body := #[.ret (.residual "f" none 1 #[.id "x"])] })
  `(@[js_norm, grind] noncomputable def TsModel.f (x : JsNumber) : JsM JsNumber := do
      return (← TsModel.f.residual_1 x))
#guard rendersSyntax (ctorCommand
    { name := "C", source := "", fields := #[{ name := "v", ty := .number }],
      ctorParams := nums #["v"],
      ctorBody := #[.fieldSet "v" (.residual "C#constructor" none 1 #[.id "v"])],
      getters := #[], methods := #[], ctorTainted := true })
  `(@[js_norm, grind] noncomputable def TsModel.C.construct (v : JsNumber) :
      JsM TsModel.C := do
      let «this.v» : JsNumber := (← TsModel.C.construct.residual_1 v)
      return TsModel.C.mk «this.v»)
#guard rendersSyntax (getterCommand
    { name := "C", source := "", fields := #[], ctorParams := #[], ctorBody := #[],
      getters := #[], methods := #[] }
    { name := "g", body := #[.ret (.residual "C#g" none 1 #[.selfRef])], tainted := true })
  `(@[js_norm, grind] noncomputable def TsModel.C.g (self : TsModel.C) :
      JsM JsNumber := do
      return (← TsModel.C.g.residual_1 self))

-- A discarded expression evaluates for its effect alone.
#guard rendersSyntax (fnCommand
    { name := "f", params := nums #["x"], source := "",
      body := #[.discard (.residual "f" none 1 #[.id "x"]), .ret (.id "x")] })
  `(@[js_norm, grind] def TsModel.f (x : JsNumber) : JsM JsNumber := do
      let _ ← TsModel.f.residual_1 x
      return x)
