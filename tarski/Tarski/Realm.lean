import Tarski.Value

/-! The realm: the intrinsics a script starts with, at fixed heap
references.

`Heap.initial` is a literal. Every intrinsic's reference is a constant
this file names, so `throwJsError` can allocate an error with the right
prototype without reading the heap to find one, a proof carries the realm
as data `simp` can compute with, and `Test/Tarski/RealmTest.lean` can pin
the literal against the constants so the two cannot drift apart.

| Reference | Intrinsic                                                |
| --------- | -------------------------------------------------------- |
| 0–6       | the seven `Error` prototypes, in `ErrorKind.all`'s order |
| 7–13      | the seven `Error` constructors, in the same order        |
| 14        | `Error.prototype.toString`                               |
| 15        | `Object.prototype`                                       |
| 16        | `Object`                                                 |
| 17–19     | `Object.prototype.hasOwnProperty`, `Object.is`, `Object.keys` |
| 20        | `Array.prototype`                                        |
| 21        | `Array`                                                  |
| 22–24     | `Array.prototype.push`, `Array.prototype.join`, `Array.isArray` |
| 25        | `String`                                                 |

The ten global bindings are cells 0–9: the seven `Error` constructors,
then `Object`, `Array`, and `String`.

`Object.prototype` exists as of #380, and it carries `hasOwnProperty`
and nothing else: `toString`, `valueOf`, and the rest of its surface are
#389's, so `{} + 1` still throws where an engine answers
`"[object Object]1"`. Object literals, function `prototype` objects,
`Error.prototype`, and `Array.prototype` all link to it. Every
`[[Prototype]]` that ought to be `Function.prototype` is still null,
that intrinsic being #389's too, and a chain that would reach one ends
instead. What is *not* faked is the part this slice observes — each
subclass prototype links to `Error.prototype` and each subclass
constructor to `Error`, which is what makes
`new TypeError("t") instanceof Error` true.

`Array.prototype` is itself an Array exotic object of length 0, as the
spec has it, which is why `Array.isArray(Array.prototype)` is true.

Property attributes are absent with descriptors (#389), so `name`,
`message`, `constructor`, and `prototype` are ordinary data properties a
script can overwrite. -/

namespace Tarski

open Js

/-- The kind's `prototype` object: 0–6, in `ErrorKind.all`'s order. -/
def ErrorKind.protoRef : ErrorKind → Ref
  | .error => 0
  | .typeError => 1
  | .rangeError => 2
  | .referenceError => 3
  | .syntaxError => 4
  | .evalError => 5
  | .uriError => 6

/-- The kind's constructor object: 7–13, just past the prototypes. -/
def ErrorKind.ctorRef (k : ErrorKind) : Ref := 7 + k.protoRef

/-- `Error.prototype.toString`, the one intrinsic of the `Error`
hierarchy that is not a constructor or a prototype. -/
def errorToStringRef : Ref := 14

/-- `Object.prototype`: the root of every ordinary prototype chain. -/
def objectProtoRef : Ref := 15

/-- `Object`. -/
def objectCtorRef : Ref := 16

/-- `Object.prototype.hasOwnProperty`. -/
def objectHasOwnPropertyRef : Ref := 17

/-- `Object.is`. -/
def objectIsRef : Ref := 18

/-- `Object.keys`. -/
def objectKeysRef : Ref := 19

/-- `Array.prototype`, itself an array of length 0. -/
def arrayProtoRef : Ref := 20

/-- `Array`. -/
def arrayCtorRef : Ref := 21

/-- `Array.prototype.push`. -/
def arrayPushRef : Ref := 22

/-- `Array.prototype.join`. -/
def arrayJoinRef : Ref := 23

/-- `Array.isArray`. -/
def arrayIsArrayRef : Ref := 24

/-- `String`. It has no `prototype` property yet: the wrapper object and
`String.prototype` are #391's. -/
def stringCtorRef : Ref := 25

/-- The cell the kind's global binding lives in: 0–6, in the same
order. -/
def ErrorKind.cellRef : ErrorKind → CellRef
  | .error => 0
  | .typeError => 1
  | .rangeError => 2
  | .referenceError => 3
  | .syntaxError => 4
  | .evalError => 5
  | .uriError => 6

/-- The cell `Object` is bound in. -/
def objectCellRef : CellRef := 7

/-- The cell `Array` is bound in. -/
def arrayCellRef : CellRef := 8

/-- The cell `String` is bound in. -/
def stringCellRef : CellRef := 9

/-- The scope a script's own declarations are instantiated on top of:
`ErrorKind.all.map (fun k => (k.name, k.cellRef))`, written out so that
`simp` sees a literal list. There is no global *object* yet (#381), so a
binding here is an ordinary cell and `globalThis` is absent. -/
def globalEnv : Env :=
  [ ("Error", 0),
    ("TypeError", 1),
    ("RangeError", 2),
    ("ReferenceError", 3),
    ("SyntaxError", 4),
    ("EvalError", 5),
    ("URIError", 6),
    ("Object", 7),
    ("Array", 8),
    ("String", 9) ]

/-- The heap a script starts from: the realm, laid out at the references
above. -/
def Heap.initial : Heap where
  -- The seven global constructor bindings, cells 0–6. They are writable:
  -- a script may assign to `Error`, as it may to any global function
  -- binding.
  cells :=
    #[ { mutable := true, value := some (.obj 7) },   -- Error
       { mutable := true, value := some (.obj 8) },   -- TypeError
       { mutable := true, value := some (.obj 9) },   -- RangeError
       { mutable := true, value := some (.obj 10) },  -- ReferenceError
       { mutable := true, value := some (.obj 11) },  -- SyntaxError
       { mutable := true, value := some (.obj 12) },  -- EvalError
       { mutable := true, value := some (.obj 13) },  -- URIError
       { mutable := true, value := some (.obj 16) },  -- Object
       { mutable := true, value := some (.obj 21) },  -- Array
       { mutable := true, value := some (.obj 25) } ] -- String
  objects :=
    #[ -- 0: Error.prototype. `toString` is on it because the binary's
       -- uncaught-error report runs that algorithm anyway.
       { proto := some 15,
         properties :=
           [ ("constructor", .obj 7),
             ("name", .prim (.str "Error")),
             ("message", .prim (.str "")),
             ("toString", .obj 14) ] },
       -- 1: TypeError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", .obj 8),
             ("name", .prim (.str "TypeError")),
             ("message", .prim (.str "")) ] },
       -- 2: RangeError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", .obj 9),
             ("name", .prim (.str "RangeError")),
             ("message", .prim (.str "")) ] },
       -- 3: ReferenceError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", .obj 10),
             ("name", .prim (.str "ReferenceError")),
             ("message", .prim (.str "")) ] },
       -- 4: SyntaxError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", .obj 11),
             ("name", .prim (.str "SyntaxError")),
             ("message", .prim (.str "")) ] },
       -- 5: EvalError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", .obj 12),
             ("name", .prim (.str "EvalError")),
             ("message", .prim (.str "")) ] },
       -- 6: URIError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", .obj 13),
             ("name", .prim (.str "URIError")),
             ("message", .prim (.str "")) ] },
       -- 7: Error. A subclass constructor's `[[Prototype]]` is `Error`
       -- itself, which is what `TypeError instanceof Error`-shaped
       -- lookups walk; `Error`'s own is Function.prototype in a real
       -- realm and null here.
       { proto := none,
         properties := [("prototype", .obj 0)],
         callable := some (.native (.errorCtor .error)) },
       -- 8: TypeError
       { proto := some 7,
         properties := [("prototype", .obj 1)],
         callable := some (.native (.errorCtor .typeError)) },
       -- 9: RangeError
       { proto := some 7,
         properties := [("prototype", .obj 2)],
         callable := some (.native (.errorCtor .rangeError)) },
       -- 10: ReferenceError
       { proto := some 7,
         properties := [("prototype", .obj 3)],
         callable := some (.native (.errorCtor .referenceError)) },
       -- 11: SyntaxError
       { proto := some 7,
         properties := [("prototype", .obj 4)],
         callable := some (.native (.errorCtor .syntaxError)) },
       -- 12: EvalError
       { proto := some 7,
         properties := [("prototype", .obj 5)],
         callable := some (.native (.errorCtor .evalError)) },
       -- 13: URIError
       { proto := some 7,
         properties := [("prototype", .obj 6)],
         callable := some (.native (.errorCtor .uriError)) },
       -- 14: Error.prototype.toString
       { callable := some (.native .errorToString) },
       -- 15: Object.prototype. The root of every ordinary chain, and
       -- itself null-prototyped. `hasOwnProperty` is the whole of its
       -- surface until #389.
       { proto := none,
         properties :=
           [ ("constructor", .obj 16),
             ("hasOwnProperty", .obj 17) ] },
       -- 16: Object
       { properties :=
           [ ("prototype", .obj 15),
             ("is", .obj 18),
             ("keys", .obj 19) ],
         callable := some (.native .objectCtor) },
       -- 17: Object.prototype.hasOwnProperty
       { callable := some (.native .objectHasOwnProperty) },
       -- 18: Object.is
       { callable := some (.native .objectIs) },
       -- 19: Object.keys
       { callable := some (.native .objectKeys) },
       -- 20: Array.prototype, an array of length 0.
       { proto := some 15,
         properties :=
           [ ("constructor", .obj 21),
             ("push", .obj 22),
             ("join", .obj 23) ],
         kind := .array 0 },
       -- 21: Array
       { properties :=
           [ ("prototype", .obj 20),
             ("isArray", .obj 24) ],
         callable := some (.native .arrayCtor) },
       -- 22: Array.prototype.push
       { callable := some (.native .arrayPush) },
       -- 23: Array.prototype.join
       { callable := some (.native .arrayJoin) },
       -- 24: Array.isArray
       { callable := some (.native .arrayIsArray) },
       -- 25: String. No `prototype` property: the wrapper is #391's, so
       -- `new String("x")` refuses until then.
       { callable := some (.native .stringCtor) } ]

end Tarski
