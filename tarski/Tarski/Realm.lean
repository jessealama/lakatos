import Tarski.Value

/-! The realm: the intrinsics a script starts with, at fixed heap
references.

`Heap.initial` is a literal. Every intrinsic's reference is a constant
this file names, so `throwJsError` can allocate an error with the right
prototype without reading the heap to find one, a proof carries the realm
as data `simp` can compute with, and `Test/Tarski/RealmTest.lean` can pin
the literal against the constants so the two cannot drift apart. The
layout is: the seven `Error` prototypes at 0–6 in `ErrorKind.all`'s
order, the seven constructors at 7–13 in the same order, and
`Error.prototype.toString` at 14. The seven global bindings are cells
0–6, holding the constructors.

Every `[[Prototype]]` that ought to be `Function.prototype` or
`Object.prototype` is null here: those intrinsics are #389's, and until
they exist a chain that would reach one ends instead. What is *not*
faked is the part this slice observes — each subclass prototype links to
`Error.prototype` and each subclass constructor to `Error`, which is what
makes `new TypeError("t") instanceof Error` true.

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

/-- `Error.prototype.toString`, the one intrinsic that is not a
constructor or a prototype. -/
def errorToStringRef : Ref := 14

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
    ("URIError", 6) ]

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
       { mutable := true, value := some (.obj 13) } ] -- URIError
  objects :=
    #[ -- 0: Error.prototype. Its own `[[Prototype]]` is Object.prototype
       -- in a real realm and null here; `toString` is on it because the
       -- binary's uncaught-error report runs that algorithm anyway.
       { proto := none,
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
       { callable := some (.native .errorToString) } ]

end Tarski
