import Tarski.Simp

/-! A `for`-`of` reduced under `simp`, one *iteration* at a time.

`evalForOf` recurses until an iterator says stop, which `simp` cannot
see, so it is never in `tarski_eval` and its equation is `rw`'s —
`Test/Tarski/ForUnfoldTest.lean`'s rule, not
`Test/Tarski/ForInUnfoldTest.lean`'s: there the `rw` count is the
prototype depth, here it is the **iteration count plus one**, the last
`rw` being the step that finds the iterator done.

Everything inside one iteration reduces without help, and that is what
this file is really pinning: `iteratorStep`, `bindForIn`, `bindPattern`,
`writeLeaf`, and — because `callIteratorNative` **is** in the set, unlike
`callReflectNative` and its two neighbours — `%ArrayIteratorPrototype%`'s
`next` all unfold in the set, so one step of the array iterator costs no
lemma list at all.

The heap is built by hand rather than run up from `Heap.initial`, for
`ForInUnfoldTest`'s reason: what this file is about is the shape of the
loop, and three objects show that as well as a realm does. -/

open Tarski

/-- Object 0 is the array `[1, 2]`; object 1 is an array iterator over
it, positioned at the start; object 2 is that iterator's `next`. Cell 0
is the number the body accumulates into. -/
private def heap : Heap :=
  { cells := #[{ mutable := true, value := some (.prim (.num 0.0)) }],
    objects :=
      #[ { kind := .array 2 true,
           properties :=
             [ ("0", Property.ordinary (.prim (.num 1.0))),
               ("1", Property.ordinary (.prim (.num 2.0))) ] },
         { kind := .arrayIterator (some (.obj 0)) .values 0 },
         Obj.builtin .arrayIteratorNext "next" 0 ] }

/-- The scope the body runs in: `s` alone, the head's own binding being
`bindForIn`'s to push. -/
private def env : Env := [("s", 0)]

/-- `s = s + v;` -/
private def body : Stmt :=
  .exprStmt (.assign (.ident "s") (.binary .add (.ident "s") (.ident "v")))

/-- The iterator record GetIterator would have built. -/
private def record : IteratorRecord := { iterator := .obj 1, next := .obj 2 }

/-- `for (const v of [1, 2]) s = s + v;`, entered with the iterator
already made. -/
private def run : Option (Except Completion (Option Value) × Heap) :=
  ((evalForOf env [] (.decl .«const» "v") body record none).run).run heap

/-- What `s` holds when the loop is over. -/
private def accumulated : Option Value :=
  run.bind (fun p => (p.2.read 0).bind (·.value))

-- The evaluator's non-loop equations plus the iterator's own.
-- `applyCoercing_prim` and `toNumberValue_prim` (`Tarski/Simp.lean`) are
-- the two ground lemmas that close a coercion of a primitive in one
-- rewrite.
attribute [local simp] evalExpr evalNamed evalStmt evalStmts bindForIn
  bindPattern evalLeafRef writeLeaf patternLeafRef Pattern.boundNames targetBoundNames allocNames
  iteratorStep createIterResult callFunction callNative callIteratorNative
  toLengthValue toIntegerOrInfinityValue toNumberValue toNumberPrim
  DeclKind.isMutable
  allocCell getCell readCell writeCell initCell putIdent
  allocObj newObject readObj writeObj modifyObj Env.lookup
  Heap.alloc Heap.read Heap.write Heap.allocObj Heap.readObj Heap.writeObj
  Obj.ownProperty Obj.getOwnProperty Obj.getOwn Obj.define Obj.isArray Obj.arrayLength?
  Obj.setOwn propGet propSet Property.ordinary Property.value? Property.writable?
  Key.beq Key.str? Key.sym? Key.arrayIndex? arrayIndex? digitsToNat
  getProp getFrom findProperty Value.ofNat
  applyBinary BinaryOp.coerces applyCoercing toPrimitive applyCoercing_prim toNumberValue_prim
  toBooleanPrim isStrPrim toStringPrim
  attempt liftCompletion loopContinues undefValue
  ExceptT.run_bind Except.map throwJsError throwCompletion

-- The array's `length` goes through ToLength, whose integer part closes
-- by `decide` and not by `simp`; the one length this program reads is
-- therefore one lemma, as `ArraySimpTest` carries its index parse.
@[local simp] private theorem len_two :
    Js.Number.FloatOps.integerOrInfinity? 2.0 = some 2 := by decide

@[local simp] private theorem two_toFloat : (2 : Nat).toFloat = 2.0 := by decide
@[local simp] private theorem repr_zero : Nat.repr 0 = "0" := by decide
@[local simp] private theorem repr_one : Nat.repr 1 = "1" := by decide
@[local simp] private theorem bump1 : (0.0 + 1.0 : Float) = 1.0 := by decide
@[local simp] private theorem bump2 : (1.0 + 2.0 : Float) = 3.0 := by decide

/-- Two elements and the step that finds the iterator done: three `rw`s
for two iterations. -/
example : accumulated = some (.prim (.num 3.0)) := by
  simp [accumulated, run, heap, env, body, record]
  rw [evalForOf]; simp        -- the first element, 1
  rw [evalForOf]; simp        -- the second, 2
  rw [evalForOf]; simp        -- the iterator is done and the loop ends

/-- info: some (Tarski.Value.prim (Js.JsVal.num 3.000000)) -/
#guard_msgs in
#eval repr accumulated
