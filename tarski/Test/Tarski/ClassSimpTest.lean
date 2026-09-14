import Tarski.Simp

/-! A closed program that defines a class, constructs one instance, and
reads a property off it reduces to its result under `simp`.

This is the shape the correspondence proof needs over classes, as
`CallSimpTest` is over calls and `ObjectSimpTest` over objects: class
definition, `[[Construct]]`, field initialization, and a property read
are ordinary equations, so `simp` runs the whole thing symbolically.
Everything the class machinery is made of — `evalClass`,
`constructClass`, `runConstructor`, `initFields`, `defineMethods` —
recurses on syntax or not at all, so all of it is in `tarski_eval`.

Nothing is unfolded by hand any more. `construct` and the prototype
*steps* recurse on the heap rather than on syntax, so they are in the set
as the guarded simprocs `Tarski/Simp.lean` declares: each fires on a
literal reference and declines on one the heap has not resolved, which is
the same condition the three `rw` lines this proof used to carry were
waiting for. `getFrom` and `findProperty` are ordinary members — they
answer an own property without recursing — so the read at the end costs
nothing either way.

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

-- A class evaluation allocates a prototype, a constructor object, and a
-- cell per declared name before the constructor's first statement runs,
-- and the realm the whole thing sits on is eighty-eight objects, so
-- `simp`'s own recursion and the kernel's check both need more room than
-- an earlier program's. That whole-program `simp` has a ceiling the
-- heap's representation sets is #471's.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
example : runProgram plain = some (.ok (some (.prim (.num 3.0)))) := by
  simp [tarski_eval, plain]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 3.000000)))) -/
#guard_msgs in
#eval repr (runProgram plain)

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 2.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
