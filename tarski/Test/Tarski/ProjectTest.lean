import Tarski.Project

/-! The projection, run on closed programs.

`Tarski/Project.lean` states what a run amounts to in a model's terms;
this file checks that claim against the evaluator, one closed program at
a time. Every case carries its JS source in a comment. What the symbolic
obligations look like is `Test/Tarski/ProjectSimpTest.lean`'s business;
what is here is the other half — `project` is total and computable, so
`#eval` prints an outcome for every shape a run can have.

The three-constructor claim is the one to watch: `other` is where a
correspondence *fails*, so every arm that answers it is written out
rather than left to a catch-all. -/

open Tarski Js

/-! ### The five arms of the projection -/

/-- `5;` -/
private def five : Program := [.exprStmt (.numLit 5.0)]

/-- info: some (Tarski.Outcome.value 5.000000) -/
#guard_msgs in
#eval repr (project readNumber (runScript five))

/-- `let x = 1;` — a declaration has no completion value. -/
private def declOnly : Program :=
  [.varDecl .«let» [{ target := "x", init := some (.numLit 1.0) }]]

/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readNumber (runScript declOnly))

/-- `undefined;` — a value the reader refuses. -/
private def undef : Program := [.exprStmt .undefLit]

/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readNumber (runScript undef))

/-- `throw new RangeError("x");` -/
private def thrownRange : Program :=
  [.throwStmt (.new (.ident "RangeError") [.strLit "x"])]

/-- info: some (Tarski.Outcome.error "RangeError") -/
#guard_msgs in
#eval repr (project readNumber (runScript thrownRange))

-- `throw new K();` for each of the seven kinds. The name comes off the
-- `[[Prototype]]` table, so this is the whole of `errorKindOf`'s domain.
#guard ErrorKind.all.all fun k =>
  project readNumber (runScript [.throwStmt (.new (.ident k.name) [])])
    == some (.error k.name)

/-- `throw 1;` — a thrown primitive is no kind at all. -/
private def thrownOne : Program := [.throwStmt (.numLit 1.0)]

/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readNumber (runScript thrownOne))

/-- `throw {};` — nor is a thrown object off `Object.prototype`. -/
private def thrownObj : Program := [.throwStmt (.objectLit [])]

/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readNumber (runScript thrownObj))

/-- `class E extends RangeError {} throw new E();` — the instance carries
`E.prototype`, not `RangeError.prototype`, so the model has no kind for
it. #478 records that as a residual site rather than a correspondence. -/
private def thrownSubclass : Program :=
  [ .classDecl "E"
      { name := some "E", superClass := some (.ident "RangeError"), elements := [] },
    .throwStmt (.new (.ident "E") []) ]

/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readNumber (runScript thrownSubclass))

/-- `return 1;` at the top level — an abrupt completion that is not a
throw. -/
private def topReturn : Program := [.returnStmt (some (.numLit 1.0))]

/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readNumber (runScript topReturn))

-- Divergence is not an outcome: it stays `none` on the other side too.
#guard (project readNumber (α := JsNumber) none) == none

-- A model is never `other`, which is what makes an obligation say
-- something. Both of `JsM`'s arms, injected.
#guard Outcome.ofModel (α := JsNumber) (.error (.error "type-projection"))
  == Outcome.error "type-projection"
#guard Outcome.ofModel (.ok (5.0 : JsNumber)) == Outcome.value 5.0

/-! ### The readers -/

/-- `true;` -/
private def boolProgram : Program := [.exprStmt (.boolLit true)]

/-- info: some (Tarski.Outcome.value true) -/
#guard_msgs in
#eval repr (project readBool (runScript boolProgram))

/-- `"hi";` — the reader for a slot a model types as `JsVal`. -/
private def strProgram : Program := [.exprStmt (.strLit "hi")]

/-- info: some (Tarski.Outcome.value (Js.JsVal.str "hi")) -/
#guard_msgs in
#eval repr (project readPrim (runScript strProgram))

private def readFieldA (h : Heap) (v : Value) : Option Value := readOwnField h v "a"

/-- `({ a: 1 });` -/
private def objectA : Program := [.exprStmt (.objectLit [.init "a" (.numLit 1.0)])]

/-- info: some (Tarski.Outcome.value (Tarski.Value.prim (Js.JsVal.num 1.000000))) -/
#guard_msgs in
#eval repr (project readFieldA (runScript objectA))

/-- `class G { get a() { return 1; } } new G();` — an accessor property is
not a field, so the reader refuses it. -/
private def getterA : Program :=
  [ .classDecl "G"
      { name := some "G", superClass := none,
        elements := [.method .getter false "a" [] [.returnStmt (some (.numLit 1.0))]] },
    .exprStmt (.new (.ident "G") []) ]

/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readFieldA (runScript getterA))

private def readFieldM (h : Heap) (v : Value) : Option Value := readOwnField h v "m"

/-- `class B { m() { return 1; } } new B();` — `m` is on the prototype, and
an inherited property is not an own one. -/
private def inheritedM : Program :=
  [ .classDecl "B"
      { name := some "B", superClass := none,
        elements := [.method .method false "m" [] [.returnStmt (some (.numLit 1.0))]] },
    .exprStmt (.new (.ident "B") []) ]

/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readFieldM (runScript inheritedM))

/-! ### Private fields

The name is a *cell*, so the reader resolves the spelling through the
class scope the instance's constructor closed over. These cases are what
that walk rests on. -/

private def readPrivateX (h : Heap) (v : Value) : Option Value := readPrivateField h v "x"
private def readPrivateY (h : Heap) (v : Value) : Option Value := readPrivateField h v "y"

/-- `class B { #x; constructor(v) { this.#x = v; } } new B(5);` -/
private def privateB : Program :=
  [ .classDecl "B"
      { name := some "B", superClass := none,
        elements :=
          [ .field false (.«private» "x") none,
            .ctor ["v"] [.exprStmt (.assign (.privateMember .this "x") (.ident "v"))] ] },
    .exprStmt (.new (.ident "B") [.numLit 5.0]) ]

/-- info: some (Tarski.Outcome.value (Tarski.Value.prim (Js.JsVal.num 5.000000))) -/
#guard_msgs in
#eval repr (project readPrivateX (runScript privateB))

-- A spelling the class does not declare is not in its scope.
/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readPrivateY (runScript privateB))

-- A primitive has no private elements and no constructor to ask.
/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readPrivateX (runScript five))

/-- `class C {} new C();` — the spelling is nowhere in *this* class's
scope, so the walk finds no name to look up. -/
private def privateless : Program :=
  [ .classDecl "C" { name := some "C", superClass := none, elements := [] },
    .exprStmt (.new (.ident "C") []) ]

/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readPrivateX (runScript privateless))

/-- `class B { #x; constructor(v) { this.#x = v; } }
class C { #x; constructor(v) { this.#x = v; } } new C(7);` — two classes,
one spelling, two cells. The reader resolves the name through the
instance's own constructor, so it answers `C`'s field and not `B`'s. -/
private def twoClasses : Program :=
  [ .classDecl "B"
      { name := some "B", superClass := none,
        elements :=
          [ .field false (.«private» "x") none,
            .ctor ["v"] [.exprStmt (.assign (.privateMember .this "x") (.ident "v"))] ] },
    .classDecl "C"
      { name := some "C", superClass := none,
        elements :=
          [ .field false (.«private» "x") none,
            .ctor ["v"] [.exprStmt (.assign (.privateMember .this "x") (.ident "v"))] ] },
    .exprStmt (.new (.ident "C") [.numLit 7.0]) ]

/-- info: some (Tarski.Outcome.value (Tarski.Value.prim (Js.JsVal.num 7.000000))) -/
#guard_msgs in
#eval repr (project readPrivateX (runScript twoClasses))

/-- `class B { #x; constructor(v) { this.#x = v; } }
B.prototype.constructor = 1; new B(5);` — the walk's one assumption, put
out. A program that overwrote `constructor` reads `none`, which projects
to `other`: the safe direction. -/
private def clobberedCtor : Program :=
  [ .classDecl "B"
      { name := some "B", superClass := none,
        elements :=
          [ .field false (.«private» "x") none,
            .ctor ["v"] [.exprStmt (.assign (.privateMember .this "x") (.ident "v"))] ] },
    .exprStmt (.assign (.member (.member (.ident "B") "prototype") "constructor") (.numLit 1.0)),
    .exprStmt (.new (.ident "B") [.numLit 5.0]) ]

/-- info: some (Tarski.Outcome.other) -/
#guard_msgs in
#eval repr (project readPrivateX (runScript clobberedCtor))
