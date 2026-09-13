import Tarski.Realm

/-! The realm's literal against the realm's constants.

`Heap.initial` is written out by hand, and every reference into it —
`ErrorKind.protoRef`, `ctorRef`, `errorToStringRef`, `cellRef` — is a
constant written out beside it. Nothing makes the two agree except this
file: a prototype moved without its constant, or a constructor pointing
at the wrong `prototype`, would be a realm that is quietly wrong
everywhere rather than a build that fails. So each case below reads one
of the layout's claims back out of the literal by its constant. -/

open Tarski

/-! ## The shape -/

#guard Heap.initial.cells.size == 7
#guard Heap.initial.objects.size == 15

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
      && o.proto == (if k == .error then none else some ErrorKind.error.protoRef)

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

#guard globalEnv.length == 7

/-! ## `Error.prototype.toString` -/

#guard match Heap.initial.readObj errorToStringRef with
  | some { callable := some (.native .errorToString), .. } => true
  | _ => false
