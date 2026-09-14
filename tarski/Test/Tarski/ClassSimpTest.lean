import Tarski.Eval

/-! A closed program that defines a class, constructs one instance, and
reads a property off it reduces to its result under `simp`.

This is the shape the correspondence proof needs over classes, as
`CallSimpTest` is over calls and `ObjectSimpTest` over objects: class
definition, `[[Construct]]`, field initialization, and a property read
are ordinary equations, so `simp` runs the whole thing symbolically.
Everything the class machinery is made of — `evalClass`,
`constructClass`, `runConstructor`, `initFields`, `defineMethods` —
recurses on syntax or not at all, so all of it is in the set.

Two definitions are unfolded by hand. `construct` is one: it is not
recursive in itself, but `callFunction`'s `Error`-constructor arm calls
it and it calls `callFunction` back, so a simp set holding both descends
through the pair forever. `findAccessorUp` is the other, for the reason
`ObjectSimpTest` records: it is a prototype *step*, and a step recurses
on the heap rather than on syntax. `getFrom` and `findAccessor`
themselves answer an own property without recursing and so are in the
set, which is why the read at the end costs no `rw` at all.

**What is not here, and why.** The issue's own program — `class Box {
#v; constructor(v) { this.#v = v; } get v() { return this.#v; } } new
Box(2).v;` — is past what Lean's kernel will check. A whole-program
`simp` reduction carries the heap through one term per state operation,
and the cost of checking the resulting proof grows faster than the chain
does: a class that carries a *method* is over the edge, and so is a
plain program that allocates six objects and does nothing else, on this
branch and on `main` alike. The ceiling is the heap's representation,
not the class machinery, and #471 owns it. Until then the program below
is the largest class program that reduces, and the getter's answer is
pinned by `#eval` rather than proved. -/

open Tarski

/-- `class A { constructor(v) { this.x = v; } } new A(3).x;` -/
private def plain : Program :=
  [ .classDecl "A"
      { name := some "A", superClass := none,
        elements := [.ctor ["v"] [.exprStmt (.assign (.member .this "x") (.ident "v"))]] },
    .exprStmt (.member (.new (.ident "A") [.numLit 3.0]) "x") ]

/-- `class Box { #v; constructor(v) { this.#v = v; } get v() { return this.#v; } }
new Box(2).v;` — the issue's example, run rather than reduced. -/
private def program : Program :=
  [ .classDecl "Box"
      { name := some "Box", superClass := none,
        elements :=
          [ .field false (.«private» "v") none,
            .ctor ["v"] [.exprStmt (.assign (.privateMember .this "v") (.ident "v"))],
            .method .getter false "v" [] [.returnStmt (some (.privateMember .this "v"))] ] },
    .exprStmt (.member (.new (.ident "Box") [.numLit 2.0]) "v") ]

-- `CallSimpTest`'s set plus everything a class is made of: the class
-- machinery, the two `Obj` definition operations and the lists they
-- keep, the private elements, the three new reserved-name constants, and
-- `attempt`, which `runConstructor` catches the body's `return` with.
attribute [local simp] evalExpr evalExprs evalStmt evalStmts evalDeclarators
  instantiateBlock hoistNames hoistDeclarators initFunctions
  varNames varNamesStmt varNamesCases hoistVars
  callFunction catchReturn makeFunction bindParams attempt
  evalClass defineMethods initializeInstance initFields initFieldList
  constructClass runConstructor bindPrivateNames privateName
  readPrivate writePrivate addPrivate allocFromConstructor isConstructor
  ClassDef.constructor? ClassDef.instanceFields ClassDef.staticFields
  ClassDef.privateNames classFields dedupNames firstConstructor privateFieldNames
  getProp setProp getFrom findAccessor
  Obj.defineData Obj.defineAccessor Obj.getOwnAccessor Obj.getPrivate
  Obj.addPrivate Obj.setPrivate Obj.isArray
  accessorGet accessorSet accessorDrop propDrop privateGet privateSet
  applyBinary toPrimitive BinaryOp.coerces applyCoercing toNumberPrim toBooleanPrim isStrPrim
  allocCell getCell readCell writeCell initCell putIdent
  allocObj newObject readObj writeObj modifyObj
  Env.lookup Heap.alloc Heap.read Heap.write
  Heap.allocObj Heap.readObj Heap.writeObj
  Obj.getOwn Obj.setOwn propGet propSet
  undefValue thisName homeName newTargetName activeFunctionName DeclKind.isMutable
  Heap.initial globalEnv objectProtoRef runScript runProgram evalProgram
  ExceptT.run_bind Except.map throwJsError throwCompletion

-- A class evaluation allocates a prototype, a constructor object, and a
-- cell per declared name before the constructor's first statement runs,
-- so `simp`'s own recursion needs more room than an earlier program's.
set_option maxRecDepth 4000 in
example : runProgram plain = some (.ok (some (.prim (.num 3.0)))) := by
  simp [plain]
  rw [construct.eq_def]; simp      -- `new A(3)`: the dispatch onto a class constructor
  rw [findAccessorUp]; simp        -- `this.x = 3`: no setter on `A.prototype`
  rw [findAccessorUp]; simp        -- nor on `Object.prototype`

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 3.000000)))) -/
#guard_msgs in
#eval repr (runProgram plain)

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 2.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
