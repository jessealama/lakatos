import Tarski.Value

/-! ValidateAndApplyPropertyDescriptor, one row of 10.1.6.3 at a time.

`Obj.applyDescriptor` is a **pure function on an `Obj`**: `none` is the
specification's `false` and `some o` is the object with the property
replaced or appended. The throw belongs to its one caller, which is what
lets the whole table be checked here with `#guard` and no heap, no
monad, and no program — the shape a correspondence proof about property
definition will want, and the shape a reader can check against the
specification's own table line by line.

`Obj.ownKeys` is here for the same reason: OrdinaryOwnPropertyKeys is a
function of the property list and the kind alone. -/

open Tarski

/-- An object with one ordinary data property, `x`. -/
private def withX : Obj := { properties := [("x", Property.ordinary (.prim (.num 1.0)))] }

/-- `{ value: v }`. -/
private def dataOf (v : Value) : Descriptor := { value := some v }

/-- A getter, as a value: the reference is arbitrary — nothing calls
it — and SameValue on two of them is reference identity. -/
private def g₁ : Value := .obj 100
private def g₂ : Value := .obj 101

/-! ## A key that is not there

A new key takes the descriptor's fields and `false`/`undefined` for
every field the descriptor does not mention, which is why a *generic*
descriptor makes a data property with no attribute at all and the value
`undefined`. -/

#guard (({} : Obj).applyDescriptor "x" {}).bind (·.getOwnProperty "x")
  == some { slot := .data (.prim .undef) false, enumerable := false, configurable := false }

#guard (({} : Obj).applyDescriptor "x" (dataOf (.prim (.num 1.0)))).bind (·.getOwnProperty "x")
  == some { slot := .data (.prim (.num 1.0)) false,
            enumerable := false, configurable := false }

#guard (({} : Obj).applyDescriptor "x" { getter := some g₁ }).bind (·.getOwnProperty "x")
  == some { slot := .accessor { getter := some g₁ }, enumerable := false, configurable := false }

-- A new key on a non-extensible object is refused; an *existing* one on
-- the same object is not, `[[Extensible]]` being about growth alone.
#guard (({ extensible := false : Obj }).applyDescriptor "x" {}).isNone
#guard ({ withX with extensible := false }.applyDescriptor "x"
    (dataOf (.prim (.num 2.0)))).isSome

/-! ## A configurable property takes anything

Every field may change, including the kind, and the fields the
descriptor does not mention stand. -/

#guard (withX.applyDescriptor "x" { enumerable := some false }).bind (·.getOwnProperty "x")
  == some { slot := .data (.prim (.num 1.0)) true, enumerable := false, configurable := true }

#guard (withX.applyDescriptor "x" { getter := some g₁ }).bind (·.getOwnProperty "x")
  == some { slot := .accessor { getter := some g₁ }, enumerable := true, configurable := true }

-- The mirror: an accessor redefined as data keeps its two attributes and
-- starts the value half fresh, so an unmentioned `[[Writable]]` is
-- `false`.
private def withGetter : Obj :=
  { properties :=
      [("x", { slot := .accessor { getter := some g₁ },
               enumerable := true, configurable := true })] }

#guard (withGetter.applyDescriptor "x" (dataOf (.prim (.num 1.0)))).bind (·.getOwnProperty "x")
  == some { slot := .data (.prim (.num 1.0)) false, enumerable := true, configurable := true }

/-! ## A non-configurable property

Six refusals: becoming configurable, flipping enumerability, changing
kind, taking a different value while non-writable, becoming writable,
and exchanging an accessor half. An identical redefinition is not a
change and is accepted. -/

private def locked : Obj :=
  { properties :=
      [("x", { slot := .data (.prim (.num 1.0)) false,
               enumerable := false, configurable := false })] }

#guard (locked.applyDescriptor "x" { configurable := some true }).isNone
#guard (locked.applyDescriptor "x" { enumerable := some true }).isNone
#guard (locked.applyDescriptor "x" { getter := some g₁ }).isNone
#guard (locked.applyDescriptor "x" { writable := some true }).isNone
#guard (locked.applyDescriptor "x" (dataOf (.prim (.num 2.0)))).isNone

-- The identity cases: every field restated as it already is.
#guard (locked.applyDescriptor "x"
    { value := some (.prim (.num 1.0)), writable := some false,
      enumerable := some false, configurable := some false }).isSome
#guard (locked.applyDescriptor "x" {}).isSome

-- SameValue, not `===`: `NaN` is the same value as `NaN`, and `-0` is
-- not the same value as `+0`.
private def lockedNaN : Obj :=
  { properties :=
      [("x", { slot := .data (.prim (.num Js.Number.NaN)) false,
               enumerable := false, configurable := false })] }
private def lockedZero : Obj :=
  { properties :=
      [("x", { slot := .data (.prim (.num 0.0)) false,
               enumerable := false, configurable := false })] }

#guard (lockedNaN.applyDescriptor "x" (dataOf (.prim (.num Js.Number.NaN)))).isSome
#guard (lockedZero.applyDescriptor "x" (dataOf (.prim (.num (-0.0))))).isNone

-- A non-configurable but *writable* data property takes a new value:
-- 10.1.6.3 step 4.e is reached only when `[[Writable]]` is false.
private def lockedWritable : Obj :=
  { properties :=
      [("x", { slot := .data (.prim (.num 1.0)) true,
               enumerable := false, configurable := false })] }

#guard (lockedWritable.applyDescriptor "x" (dataOf (.prim (.num 2.0)))).bind
    (·.getOwnProperty "x")
  == some { slot := .data (.prim (.num 2.0)) true,
            enumerable := false, configurable := false }
-- It may still be made non-writable — that is the one attribute change a
-- non-configurable property has left — but not back again.
#guard (lockedWritable.applyDescriptor "x" { writable := some false }).isSome

-- A non-configurable accessor refuses a different half and accepts the
-- same one; an absent half leaves what is there standing.
private def lockedAccessor : Obj :=
  { properties :=
      [("x", { slot := .accessor { getter := some g₁ },
               enumerable := false, configurable := false })] }

#guard (lockedAccessor.applyDescriptor "x" { getter := some g₂ }).isNone
#guard (lockedAccessor.applyDescriptor "x" { setter := some g₁ }).isNone
#guard (lockedAccessor.applyDescriptor "x" { getter := some g₁ }).isSome
#guard (lockedAccessor.applyDescriptor "x" { setter := some (.prim .undef) }).isSome

/-! ## FromPropertyDescriptor's other direction

A property read as the fully populated descriptor 6.2.6 says it is, with
an absent accessor half reading `undefined`. -/

#guard (Property.ordinary (.prim (.num 1.0))).toDescriptor
  == { value := some (.prim (.num 1.0)), writable := some true,
       enumerable := some true, configurable := some true }

#guard ({ slot := .accessor { getter := some g₁ },
          enumerable := false, configurable := true } : Property).toDescriptor
  == { getter := some g₁, setter := some (.prim .undef),
       enumerable := some false, configurable := some true }

/-! ## The six attribute shapes the realm and the evaluator use -/

#guard (Property.ordinary (.prim .undef)).enumerable
  && (Property.ordinary (.prim .undef)).configurable
  && (Property.ordinary (.prim .undef)).writable? == some true
#guard !(Property.method (.prim .undef)).enumerable
  && (Property.method (.prim .undef)).configurable
  && (Property.method (.prim .undef)).writable? == some true
#guard !(Property.attribute (.prim .undef)).enumerable
  && (Property.attribute (.prim .undef)).configurable
  && (Property.attribute (.prim .undef)).writable? == some false
#guard !(Property.constant (.prim .undef)).enumerable
  && !(Property.constant (.prim .undef)).configurable
  && (Property.constant (.prim .undef)).writable? == some false
#guard !(Property.functionPrototype (.prim .undef)).enumerable
  && !(Property.functionPrototype (.prim .undef)).configurable
  && (Property.functionPrototype (.prim .undef)).writable? == some true

/-! ## OrdinaryOwnPropertyKeys

Index keys in ascending numeric order, then — for an array — `length`,
then every other key in insertion order, **data and accessor properties
interleaved**, which is the ordering limit the second list used to
impose. -/

private def mixed : Obj :=
  { properties :=
      [ ("b", Property.ordinary (.prim (.num 1.0))),
        ("2", Property.ordinary (.prim (.num 1.0))),
        ("a", Property.ordinary (.prim (.num 1.0))),
        ("1", Property.ordinary (.prim (.num 1.0))) ] }

#guard mixed.ownKeys == ["1", "2", "b", "a"].map Key.str

-- An accessor defined last comes last, not before the data keys.
#guard (mixed.defineAccessorHalf "c" (some g₁) none false true).ownKeys
  == ["1", "2", "b", "a", "c"].map Key.str

-- An array's `length` is an own property that does not live in the
-- property list, so `ownKeys` puts it in by hand, after the indices.
#guard (Obj.array none [.prim (.num 7.0)]).ownKeys == ["0", "length"].map Key.str
#guard ((Obj.array none [.prim (.num 7.0)]).define "x"
    (Property.ordinary (.prim .undef))).ownKeys == ["0", "length", "x"].map Key.str

-- `Object.keys` and `for`-`in` see only the enumerable ones, and an
-- array's `length` is never among them.
#guard (mixed.define "hidden" (Property.method (.prim .undef))).enumerableKeys
  == ["1", "2", "b", "a"]
#guard (Obj.array none [.prim (.num 7.0)]).enumerableKeys == ["0"]

/-! ## Truncation stops at the first non-configurable element

10.4.2.4 steps 12–14: the scan runs from the top down and the index it
stops at fixes the length. An ordinary array has nothing to stop it. -/

private def threeElements : Obj :=
  Obj.array none [.prim (.num 0.0), .prim (.num 1.0), .prim (.num 2.0)]

#guard (threeElements.truncate 1).2 == 1
#guard (threeElements.truncate 1).1.ownKeys == ["0", "length"].map Key.str
#guard (threeElements.truncate 0).2 == 0

-- With element 1 non-configurable, a truncation to 0 stops there and
-- reaches 2 — one past the index it could not delete.
private def stubborn : Obj :=
  threeElements.define "1" { slot := .data (.prim (.num 1.0)) true,
                             enumerable := true, configurable := false }

#guard (stubborn.truncate 0).2 == 2
#guard (stubborn.truncate 0).1.ownKeys == ["0", "1", "length"].map Key.str

-- The `length`'s own writability is not truncation's business: the
-- caller decided whether the write was allowed at all.
#guard ({ threeElements with kind := .array 3 false }.truncate 1).1.arrayLength?
  == some (1, false)

/-! ## SetIntegrityLevel and TestIntegrityLevel -/

#guard (withX.setIntegrity false).testIntegrity false
#guard !(withX.setIntegrity false).testIntegrity true
#guard (withX.setIntegrity true).testIntegrity true
#guard ({ extensible := false : Obj }).testIntegrity true
#guard !withX.testIntegrity false

-- A frozen array's `length` is non-writable too, which is what makes
-- `Object.isFrozen(Object.freeze([1]))` true.
#guard (threeElements.setIntegrity true).arrayLength? == some (3, false)
#guard (threeElements.setIntegrity true).testIntegrity true
#guard !(threeElements.setIntegrity false).testIntegrity true

/-! ## A symbol key goes through the same table

`Obj.applyDescriptor` is a function of a `Key`, and the key's only part
in it is the lookup: a symbol-keyed property is defined, refused, and
redefined by exactly the rules above. -/

private def symKey : Key := .sym { id := 0, description := some "k" }

private def withSym : Option Obj :=
  ({ : Obj }).applyDescriptor symKey { value := some (.prim (.num 1.0)) }

#guard withSym.isSome
#guard withSym.bind (·.getOwn symKey) == some (Value.prim (.num 1.0))
-- Defined with no `writable`, so a redefinition to another value is
-- refused, exactly as a string-keyed one would be.
#guard (withSym.bind (·.applyDescriptor symKey { value := some (.prim (.num 2.0)) })).isNone
-- And a string key of the same spelling is a different property.
#guard withSym.bind (·.getOwn "k") == none
#guard withSym.map (·.ownKeys) == some [symKey]
#guard withSym.map (·.stringKeys) == some []

/-! ## A String exotic object's index (10.4.3.5)

An index below the length is synthesized from `[[StringData]]`, so there
is nothing in the property list to replace: `applyDescriptor` validates
against it through `Property.accepts` and answers the object unchanged
when the redefinition is identical, `none` when it is not. An index at or
past the length, and every non-index key, is ordinary. -/

private def strAB : Obj := Obj.stringWrapper none (Js.JsString.ofString "ab")

private def sameIndex : Descriptor :=
  { value := some (.prim (.str "a")), writable := some false,
    enumerable := some true, configurable := some false }

#guard strAB.ownProperty "0"
  == some { slot := .data (.prim (.str "a")) false, enumerable := true, configurable := false }
#guard strAB.ownProperty "1"
  == some { slot := .data (.prim (.str "b")) false, enumerable := true, configurable := false }
#guard strAB.ownProperty "2" == none
#guard strAB.ownProperty "length"
  == some { slot := .data (.prim (.num 2.0)) false, enumerable := false, configurable := false }
#guard strAB.ownKeys == (["0", "1", "length"] : List String).map Key.str
#guard strAB.enumerableKeys == ["0", "1"]
#guard strAB.isString
#guard strAB.stringData? == some (Js.JsString.ofString "ab")

-- An identical redefinition is the specification's no-op: the object
-- comes back with nothing added to its property list.
#guard (strAB.applyDescriptor "0" sameIndex).map (·.properties) == some strAB.properties
#guard (strAB.applyDescriptor "0" {}).map (·.properties) == some strAB.properties

-- A different value, a different attribute, and an accessor are each
-- refused.
#guard (strAB.applyDescriptor "0" (dataOf (.prim (.str "z")))).isNone
#guard (strAB.applyDescriptor "0" { configurable := some true }).isNone
#guard (strAB.applyDescriptor "0" { writable := some true }).isNone
#guard (strAB.applyDescriptor "0" { enumerable := some false }).isNone
#guard (strAB.applyDescriptor "0" { getter := some g₁ }).isNone

-- An index at or past the length is ordinary, and so is `length` itself:
-- `length` is a real own property, non-writable and non-configurable, so
-- a redefinition of it refuses the ordinary way.
#guard (strAB.applyDescriptor "2" (dataOf (.prim (.str "z")))).bind (·.getOwnProperty "2")
  == some { slot := .data (.prim (.str "z")) false, enumerable := false, configurable := false }
#guard (strAB.applyDescriptor "length" (dataOf (.prim (.num 5.0)))).isNone
#guard (strAB.applyDescriptor "foo" (dataOf (.prim (.num 1.0)))).bind (·.getOwnProperty "foo")
  == some { slot := .data (.prim (.num 1.0)) false, enumerable := false, configurable := false }

-- Freezing one is a no-op on the indices: they are already non-writable
-- and non-configurable.
#guard (strAB.setIntegrity true).testIntegrity true
