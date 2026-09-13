import Tarski.Realm

/-! The realm's literal against the realm's constants.

`Heap.initial` is written out by hand, and every reference into it —
`ErrorKind.protoRef`, `ctorRef`, `errorToStringRef`, `cellRef`, and the
`Object`, `Array`, and `String` references — is a constant written out
beside it. Nothing makes the two agree except this
file: a prototype moved without its constant, or a constructor pointing
at the wrong `prototype`, would be a realm that is quietly wrong
everywhere rather than a build that fails. So each case below reads one
of the layout's claims back out of the literal by its constant. -/

open Tarski

/-! ## The shape -/

#guard Heap.initial.cells.size == 12
#guard Heap.initial.objects.size == 29

/-! ## Each kind's prototype

`name` and `message` are what `Error.prototype.toString` reads, and
`constructor` is what points back; the `[[Prototype]]` link is what makes
`new TypeError("t") instanceof Error` true. -/

private def protoOf (k : ErrorKind) : Option Obj := Heap.initial.readObj k.protoRef

#guard ErrorKind.all.all fun k =>
  match protoOf k with
  | none => false
  | some o =>
    o.getOwn "name" == some (.prim (.str k.name))
      && o.getOwn "message" == some (.prim (.str ""))
      && o.getOwn "constructor" == some (.obj k.ctorRef)
      && o.proto == (if k == .error then some objectProtoRef else some ErrorKind.error.protoRef)

-- `Error.prototype` is the one that carries `toString`; the subclasses
-- inherit it.
#guard (protoOf .error).bind (fun o => o.getOwn "toString") == some (.obj errorToStringRef)
#guard (protoOf .typeError).bind (fun o => o.getOwn "toString") == none

/-! ## Each kind's constructor

`Obj` has no `DecidableEq` — a `Closure` holds syntax — so `callable` is
matched rather than compared. -/

private def ctorOf (k : ErrorKind) : Option Obj := Heap.initial.readObj k.ctorRef

#guard ErrorKind.all.all fun k =>
  match ctorOf k with
  | none => false
  | some o =>
    o.getOwn "prototype" == some (.obj k.protoRef)
      && o.proto == (if k == .error then none else some ErrorKind.error.ctorRef)
      && (match o.callable with
          | some (.native (.errorCtor k')) => k' == k
          | _ => false)

/-! ## The global bindings

Each constructor is bound under its own `name`, in a cell holding the
constructor object. -/

#guard ErrorKind.all.all fun k =>
  Env.lookup globalEnv k.name == some k.cellRef
    && (match Heap.initial.read k.cellRef with
        | some c => c.value == some (.obj k.ctorRef)
        | none => false)

#guard globalEnv.length == 12

/-! ## `Error.prototype.toString` -/

#guard match Heap.initial.readObj errorToStringRef with
  | some { callable := some (.native .errorToString), .. } => true
  | _ => false

/-! ## `Object.prototype` and `Object`

`hasOwnProperty` is the whole of `Object.prototype`'s surface: `toString`
and `valueOf` are #389's, and `ObjectsTest` pins that `{} + 1` still
throws for want of them. -/

#guard match Heap.initial.readObj objectProtoRef with
  | some o =>
    o.proto == none
      && o.getOwn "constructor" == some (.obj objectCtorRef)
      && o.getOwn "hasOwnProperty" == some (.obj objectHasOwnPropertyRef)
      && o.getOwn "toString" == none
      && o.getOwn "valueOf" == none
      && o.kind == .ordinary
  | none => false

#guard match Heap.initial.readObj objectCtorRef with
  | some o =>
    o.getOwn "prototype" == some (.obj objectProtoRef)
      && o.getOwn "is" == some (.obj objectIsRef)
      && o.getOwn "keys" == some (.obj objectKeysRef)
      && (match o.callable with
          | some (.native .objectCtor) => true
          | _ => false)
  | none => false

#guard match Heap.initial.readObj objectHasOwnPropertyRef with
  | some { callable := some (.native .objectHasOwnProperty), .. } => true
  | _ => false

#guard match Heap.initial.readObj objectIsRef with
  | some { callable := some (.native .objectIs), .. } => true
  | _ => false

#guard match Heap.initial.readObj objectKeysRef with
  | some { callable := some (.native .objectKeys), .. } => true
  | _ => false

/-! ## `Array.prototype` and `Array`

`Array.prototype` is itself an array of length 0, which the spec is
explicit about and `Array.isArray(Array.prototype)` observes. -/

#guard match Heap.initial.readObj arrayProtoRef with
  | some o =>
    o.kind == .array 0
      && o.proto == some objectProtoRef
      && o.getOwn "constructor" == some (.obj arrayCtorRef)
      && o.getOwn "push" == some (.obj arrayPushRef)
      && o.getOwn "join" == some (.obj arrayJoinRef)
  | none => false

#guard match Heap.initial.readObj arrayCtorRef with
  | some o =>
    o.getOwn "prototype" == some (.obj arrayProtoRef)
      && o.getOwn "isArray" == some (.obj arrayIsArrayRef)
      && (match o.callable with
          | some (.native .arrayCtor) => true
          | _ => false)
  | none => false

#guard match Heap.initial.readObj arrayPushRef with
  | some { callable := some (.native .arrayPush), .. } => true
  | _ => false

#guard match Heap.initial.readObj arrayJoinRef with
  | some { callable := some (.native .arrayJoin), .. } => true
  | _ => false

#guard match Heap.initial.readObj arrayIsArrayRef with
  | some { callable := some (.native .arrayIsArray), .. } => true
  | _ => false

/-! ## `String`

No `prototype` property: the wrapper object and `String.prototype` are
#391's, so `new String("x")` refuses. -/

#guard match Heap.initial.readObj stringCtorRef with
  | some o =>
    o.getOwn "prototype" == none
      && (match o.callable with
          | some (.native .stringCtor) => true
          | _ => false)
  | none => false

/-! ## The three new global bindings -/

#guard Env.lookup globalEnv "Object" == some objectCellRef
#guard Env.lookup globalEnv "Array" == some arrayCellRef
#guard Env.lookup globalEnv "String" == some stringCellRef

#guard (Heap.initial.read objectCellRef).bind (·.value) == some (.obj objectCtorRef)
#guard (Heap.initial.read arrayCellRef).bind (·.value) == some (.obj arrayCtorRef)
#guard (Heap.initial.read stringCellRef).bind (·.value) == some (.obj stringCtorRef)

/-! ## The host bindings

`print` and `$262` are what test262 asks a host for. `%PrintLog%` is the
array `print` appends to: an intrinsic nothing binds, so a run's log is
exactly what `print` put there. `$262` is empty on purpose — its hooks
are decoder refusals, and what is left is an object for `typeof` to see
and an absent `IsHTMLDDA` to read as `undefined`. -/

#guard match Heap.initial.readObj printLogRef with
  | some o => o.kind == .array 0 && o.proto == some arrayProtoRef && o.properties == []
  | none => false

#guard match Heap.initial.readObj printRef with
  | some { callable := some (.native .print), .. } => true
  | _ => false

#guard match Heap.initial.readObj hostRef with
  | some o => o.properties == [] && o.proto == some objectProtoRef && o.callable.isNone
  | none => false

#guard Env.lookup globalEnv "print" == some printCellRef
#guard Env.lookup globalEnv "$262" == some hostCellRef

#guard (Heap.initial.read printCellRef).bind (·.value) == some (.obj printRef)
#guard (Heap.initial.read hostCellRef).bind (·.value) == some (.obj hostRef)
