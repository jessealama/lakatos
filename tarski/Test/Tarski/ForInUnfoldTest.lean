import Tarski.Eval

/-! A `for`-`in` reduced under `simp`, one *object* at a time.

`Test/Tarski/ForUnfoldTest.lean` is the same shape over a `for`, where
the `rw` count is the iteration count. Here it is not, and that is the
whole point of this file: `for`-`in` recurses on two different things,
and only one of them is `rw`'s.

`evalForIn` walks a **key list**, which is data — the keys were taken
from the object when the object was reached — so `simp` reduces a whole
level without help, however many keys it has. `forInNext` is the step to
the next object on the prototype chain, a heap link like `getFromUp`'s,
and that is what is unfolded one step at a time. So the `rw` count is the
**prototype depth**: two here, one to reach the parent and one to find
that the parent has no prototype of its own, while the two keys cost
nothing.

The heap is built by hand rather than run up from `Heap.initial`.
Whole-program `simp` over the realm is exercised by
`Test/Tarski/ObjectSimpTest.lean` and its neighbours and is minutes of
wall time here, the realm being eighty-nine objects and
`Obj.ownKeys` reading every key of every level as a possible array index
(#471 is the ceiling that sets). What this file is about is the shape of
the enumeration, which two objects show as well as a realm does.
`Test/Tarski/ForInTest.lean` is where the behaviour is checked. -/

open Tarski

/-- A child with one own key, whose prototype has one of its own. Cell 0
is the string the body accumulates into. -/
private def heap : Heap :=
  { cells := #[{ mutable := true, value := some (.prim (.str "")) }],
    objects :=
      #[ { proto := some 1, properties := [("a", Property.ordinary (.prim (.num 1.0)))] },
         { properties := [("b", Property.ordinary (.prim (.num 2.0)))] } ] }

/-- The scope the body runs in: `s` alone, the head's own binding being
`bindForIn`'s to push. -/
private def env : Env := [("s", 0)]

/-- `s = s + k;` -/
private def body : Stmt :=
  .exprStmt (.assign (.ident "s") (.binary .add (.ident "s") (.ident "k")))

/-- `for (const k in child) s = s + k;`, entered at the child with its
own keys already taken. -/
private def run : Option (Except Completion (Option Value) × Heap) :=
  ((evalForIn env [] (.decl .«const» "k") body 0 ["a"] [] none).run).run heap

/-- What `s` holds when the enumeration is over. -/
private def accumulated : Option Value :=
  run.bind (fun p => (p.2.read 0).bind (·.value))

-- The evaluator's non-loop equations plus the enumeration's own. `evalForIn`
-- and `bindForIn` are in the set and `forInNext` is not: the first two run
-- out with the key list, the third is the chain.
attribute [local simp] evalExpr evalNamed evalStmt evalStmts evalForIn bindForIn
  DeclKind.isMutable
  allocCell getCell readCell writeCell initCell putIdent
  readObj writeObj Env.lookup Heap.alloc Heap.read Heap.write Heap.readObj
  Obj.ownProperty Obj.getOwnProperty Obj.ownKeys Obj.isArray Obj.arrayLength?
  propGet arrayIndex? digitsToNat
  applyBinary BinaryOp.coerces applyCoercing toPrimitive
  toNumberPrim toBooleanPrim isStrPrim toStringPrim
  attempt liftCompletion loopContinues undefValue
  ExceptT.run_bind Except.map throwJsError throwCompletion

/-- Both levels are visited, in order, and the two `rw`s are the two
links of the chain. -/
example : accumulated = some (.prim (.str "ab")) := by
  simp [accumulated, run, heap, env, body]
  rw [forInNext]; simp        -- up to the parent, whose one own key is `b`
  rw [forInNext]; simp        -- the parent has no prototype: the walk ends

/-- info: some (Tarski.Value.prim (Js.JsVal.str "ab")) -/
#guard_msgs in
#eval repr accumulated
