import Tarski.Eval
import Tarski.Format

/-! The String exotic object: `new String(v)`, `String.prototype`, and
ToObject of a string primitive.

The arrangement is the **opposite** of the array's, and on purpose. A
String object's index properties are *synthesized* from `[[StringData]]`
— unbounded data an object should not copy — while its `length` is a real
own `constant` property, because StringCreate (10.4.3.4) defines it once
with DefinePropertyOrThrow and it can never change. That is what puts
`length` after the indices and before everything else in `ownKeys`, and
it is why `Obj.ownProperty` had to become the one `[[GetOwnProperty]]`:
`getFrom`, `findProperty`, `deleteProp`, `enumerableKeys`, and
`applyDescriptor` all read it now, so the array's `length` and the
string's indices are answered in one place.

A string *primitive* reads through `String.prototype` without allocating
a wrapper at all, exactly as a Number does, so the receiver a method gets
is the primitive; `Test/Tarski/StringBuiltinsTest.lean` is that side. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

private def expr (e : Expr) : Program := [.exprStmt e]

/-- `recv.name(args...)`. -/
private def m (recv : Expr) (name : String) (args : List Expr) : Expr :=
  .call (.member recv name) args

/-- `Object.name(args...)`. -/
private def ob (name : String) (args : List Expr) : Expr :=
  m (.ident "Object") name args

/-- `new String(<e>)`. -/
private def wrap (e : Expr) : Expr := .new (.ident "String") [e]

/-- `const s = new String("ab"); <rest>` -/
private def withS (str : String) (rest : List Stmt) : Program :=
  .varDecl .«const» [{ target := "s", init := some (wrap (.strLit str)) }] :: rest

/-! ## The object -/

#guard outcome (expr (.unary .typeof (wrap (.strLit "ab")))) == "object"
#guard outcome (expr (.member (wrap (.strLit "ab")) "length")) == "2"
#guard outcome (expr (.index (wrap (.strLit "ab")) (.numLit 1.0))) == "b"
#guard outcome (expr (.index (wrap (.strLit "ab")) (.numLit 5.0))) == "undefined"
#guard outcome (expr (.member (wrap (.strLit "😀")) "length")) == "2"
#guard outcome (expr (m (wrap (.numLit 1.0)) "valueOf" [])) == "1"
#guard outcome (expr (.binary .instanceof (wrap (.numLit 1.0)) (.ident "String"))) == "true"
#guard outcome (expr (m (.member (.ident "Object") "prototype") "toString" [])) == "[object Object]"

-- `Object.prototype.toString` reads `[[StringData]]` as `String`.
#guard outcome (expr
    (m (.member (.member (.ident "Object") "prototype") "toString") "call" [wrap (.strLit "a")]))
  == "[object String]"

/-! ## The own keys

The indices come first, then `length`, then anything a script added. -/

#guard outcome (expr (m (ob "getOwnPropertyNames" [wrap (.strLit "ab")]) "join" [])) == "0,1,length"
#guard outcome (expr (m (ob "keys" [wrap (.strLit "ab")]) "join" [])) == "0,1"
#guard outcome (expr (m (ob "keys" [.strLit "ab"]) "join" [])) == "0,1"
#guard outcome (expr (m (ob "getOwnPropertyNames" [.strLit "ab"]) "join" [])) == "0,1,length"
#guard outcome (expr (m (.strLit "abc") "hasOwnProperty" [.strLit "1"])) == "true"
#guard outcome (expr (m (.strLit "abc") "hasOwnProperty" [.strLit "3"])) == "false"
#guard outcome (expr (m (.strLit "abc") "hasOwnProperty" [.strLit "length"])) == "true"

-- `for`-`in` goes through ToObject like every other object, so a
-- property a script adds is enumerated after the indices.
#guard outcome
    (withS "ab"
      [ .exprStmt (.assign (.member (.ident "s") "foo") (.numLit 1.0)),
        .varDecl .«let» [{ target := "k", init := some (.strLit "") }],
        .forInStmt (.decl .«const» "x") (.ident "s")
          (.exprStmt (.assign (.ident "k") (.binary .add (.ident "k") (.ident "x")))),
        .exprStmt (.ident "k") ])
  == "01foo"

/-! ## The index properties' attributes

Enumerable, not writable, not configurable (10.4.3.5), and `length` is
none of the three. -/

private def descOf (o : Expr) (key : String) (field : String) : Expr :=
  .member (ob "getOwnPropertyDescriptor" [o, .strLit key]) field

#guard outcome (expr (descOf (wrap (.strLit "a")) "0" "value")) == "a"
#guard outcome (expr (descOf (wrap (.strLit "a")) "0" "writable")) == "false"
#guard outcome (expr (descOf (wrap (.strLit "a")) "0" "enumerable")) == "true"
#guard outcome (expr (descOf (wrap (.strLit "a")) "0" "configurable")) == "false"
#guard outcome (expr (descOf (wrap (.strLit "a")) "length" "value")) == "1"
#guard outcome (expr (descOf (wrap (.strLit "a")) "length" "writable")) == "false"
#guard outcome (expr (descOf (wrap (.strLit "a")) "length" "enumerable")) == "false"
#guard outcome (expr (descOf (wrap (.strLit "a")) "length" "configurable")) == "false"

/-! ## Every write refuses

A synthesized index is not in the property list, so `applyDescriptor`
validates against it through `Property.accepts` rather than replacing it:
an identical redefinition is the specification's no-op, and anything else
is refused. -/

#guard outcome (withS "ab" [.exprStmt (.delete (.index (.ident "s") (.numLit 0.0)))])
  == "uncaught: TypeError: Cannot delete property '0' of #<Object>"
#guard outcome
    (withS "ab" [.exprStmt (.assign (.index (.ident "s") (.numLit 0.0)) (.strLit "z"))])
  == "uncaught: TypeError: Cannot assign to read only property '0' of object '#<Object>'"
#guard outcome (withS "ab" [.exprStmt (.assign (.member (.ident "s") "length") (.numLit 5.0))])
  == "uncaught: TypeError: Cannot assign to read only property 'length' of object '#<Object>'"

-- An identical redefinition is accepted.
#guard outcome
    (withS "a"
      [ .exprStmt (ob "defineProperty"
          [ .ident "s", .strLit "0",
            .objectLit
              [ .init "value" (.strLit "a"), .init "writable" (.boolLit false),
                .init "enumerable" (.boolLit true), .init "configurable" (.boolLit false) ] ]),
        .exprStmt (.strLit "ok") ])
  == "ok"

-- A different value is not.
#guard outcome
    (withS "a"
      [ .exprStmt (ob "defineProperty"
          [.ident "s", .strLit "0", .objectLit [.init "value" (.strLit "b")]]) ])
  == "uncaught: TypeError: Cannot redefine property: 0"

-- An index at or past the length is ordinary, so it can be added.
#guard outcome
    (withS "a"
      [ .exprStmt (ob "defineProperty"
          [.ident "s", .strLit "1", .objectLit [.init "value" (.strLit "b")]]),
        .exprStmt (.index (.ident "s") (.numLit 1.0)) ])
  == "b"

-- An ordinary key is an ordinary write.
#guard outcome
    (withS "ab"
      [ .exprStmt (.assign (.member (.ident "s") "foo") (.numLit 1.0)),
        .exprStmt (.member (.ident "s") "foo") ])
  == "1"

-- Freezing one is a no-op on the indices, which are already frozen.
#guard outcome (expr (ob "isFrozen" [ob "freeze" [wrap (.strLit "a")]])) == "true"

/-! ## `String.prototype` is itself a String object of `""` (22.1.3) -/

#guard outcome (expr (.member (.member (.ident "String") "prototype") "length")) == "0"
#guard outcome (expr
    (m (.member (.member (.ident "Object") "prototype") "toString") "call"
      [.member (.ident "String") "prototype"]))
  == "[object String]"
#guard outcome (expr
    (.binary .strictEq (ob "getPrototypeOf" [.strLit "a"]) (.member (.ident "String") "prototype")))
  == "true"
#guard outcome (expr
    (.binary .strictEq (.member (.member (.ident "String") "prototype") "constructor")
      (.ident "String")))
  == "true"

/-! ## ToObject of a string -/

#guard outcome (expr (.unary .typeof (.call (.ident "Object") [.strLit "s"]))) == "object"
#guard outcome (expr (m (.call (.ident "Object") [.strLit "s"]) "valueOf" [])) == "s"

/-! ## A subclass

`constructNative` honours NewTarget, so the instance gets the subclass's
prototype and its `[[StringData]]` all the same. -/

#guard outcome
    [ .classDecl "S" { name := some "S", superClass := some (.ident "String"), elements := [] },
      .varDecl .«const» [{ target := "x", init := some (.new (.ident "S") [.strLit "ab"]) }],
      .exprStmt (.logical .and
        (.binary .strictEq (.member (.ident "x") "length") (.numLit 2.0))
        (.binary .instanceof (.ident "x") (.ident "S"))) ]
  == "true"
