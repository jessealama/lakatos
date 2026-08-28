import Lean.Data.Json

/-! The emission IR: the shapes `schemas/thales-emission.schema.json`
fixes, decoded strictly — an unknown kind or a missing field is a decode
error naming the offender, and the whole run fails cleanly on it. -/

namespace ThalesEmit

open Lean

inductive JsExpr where
  | num (lit : String)
  | id (name : String)
  | unop (op : String) (operand : JsExpr)
  | binop (op : String) (left right : JsExpr)
  | sameValue (left right : JsExpr)
  | mathSqrt (arg : JsExpr)
  | mathAbs (arg : JsExpr)
  | numberIsFinite (arg : JsExpr)
  | numberIsNaN (arg : JsExpr)
  | call (callee : String) (module : Option String) (args : Array JsExpr)
  | newObj (className : String) (module : Option String) (args : Array JsExpr)
  | getterRead (className : String) (module : Option String) (name : String)
      (object : JsExpr)
  | fieldRead (className : String) (module : Option String) (field : String)
      (object : JsExpr)
  | methodCall (className : String) (module : Option String) (name : String)
      (object : JsExpr) (args : Array JsExpr)
  | selfRef
deriving Repr, Inhabited

inductive JsStmt where
  | ret (expr : JsExpr)
  | throwErr (error : String)
  | constDecl (name : String) (init : JsExpr)
  | letDecl (name : String) (init : JsExpr)
  | assign (name : String) (expr : JsExpr)
  | ite (cond : JsExpr) (thn : Array JsStmt) (els : Option (Array JsStmt))
  | fieldSet (field : String) (expr : JsExpr)
deriving Repr, Inhabited

/-- A parameter's declared type: a TypeScript number, or an instance of a
modeled class, whose module is none for the entry file's own. -/
inductive ParamTy where
  | number
  | cls (name : String) (module : Option String)
deriving Repr, Inhabited, BEq

structure Param where
  name : String
  ty : ParamTy
deriving Repr, Inhabited

structure EmitFn where
  name : String
  /-- The defining module's entry-relative path; none for the entry. -/
  module : Option String := none
  params : Array Param
  source : String
  body : Array JsStmt
deriving Repr, Inhabited

structure EmitGetter where
  name : String
  body : Array JsStmt
deriving Repr, Inhabited

structure EmitMethod where
  name : String
  params : Array Param
  body : Array JsStmt
deriving Repr, Inhabited

/-- A class: the structure its fields make, the constructor that assigns
each exactly once on every path, and one function per modeled getter or
method. -/
structure EmitClass where
  name : String
  /-- The defining module's entry-relative path; none for the entry. -/
  module : Option String := none
  source : String
  /-- Field spellings in declaration order — the structure's fields. -/
  fields : Array String
  ctorParams : Array Param
  ctorBody : Array JsStmt
  getters : Array EmitGetter
  methods : Array EmitMethod := #[]
deriving Repr, Inhabited

inductive Decl where
  | fn (f : EmitFn)
  | cls (c : EmitClass)
deriving Repr, Inhabited

/-- A binder's denoted domain: a finite half-open `[lo, hi)` integer
range, the whole int line, the naturals, or the doubles a `number`
binder's bounds admit — each bound an op × endpoint-literal pair. -/
inductive BinderIR where
  | range (name : String) (lo hi : Int)
  | int (name : String)
  | nat (name : String)
  | number (name : String) (lower upper : Option (String × String))
  /-- A class-valued binder: the instance ranges over the image of the
  named class's constructor, applied to one argument per `ctorParams`. -/
  | cls (name className : String) (module : Option String)
      (ctorParams : Array String)
deriving Repr, Inhabited

def BinderIR.name : BinderIR → String
  | .range n _ _ => n
  | .int n => n
  | .nat n => n
  | .number n _ _ => n
  | .cls n .. => n

/-- Whether the binder enumerates `Int`s, so a use of it inside the body
crosses to the Float world. A `number` binder is already a double. -/
def BinderIR.isIntValued : BinderIR → Bool
  | .number .. | .cls .. => false
  | _ => true

inductive Conclusion where
  | eq (left right : JsExpr)
  | istrue (expr : JsExpr)
deriving Repr, Inhabited

/-- Guards sit inside every binder and in front of the conclusion, the
order the array carries. -/
inductive Payload where
  | structured (binders : Array BinderIR) (guards : Array JsExpr)
      (conclusion : Conclusion)
  | bare
deriving Repr, Inhabited

structure Obligation where
  function : String
  property : String
  formula : String
  payload : Payload
deriving Repr, Inhabited

structure Emission where
  file : String
  declarations : Array Decl
  obligations : Array Obligation
deriving Repr, Inhabited

def getStr (j : Json) (field : String) : Except String String := do
  match (← j.getObjVal? field).getStr? with
  | .ok s => pure s
  | .error _ => throw s!"field '{field}' is not a string"

/-- An optional string field: an absent field decodes as none, a present
non-string is an error. -/
def getStrOpt (j : Json) (field : String) : Except String (Option String) :=
  match j.getObjVal? field with
  | .error _ => pure none
  | .ok v => match v.getStr? with
    | .ok s => pure (some s)
    | .error _ => throw s!"field '{field}' is not a string"

def getArr (j : Json) (field : String) : Except String (Array Json) := do
  match (← j.getObjVal? field).getArr? with
  | .ok a => pure a
  | .error _ => throw s!"field '{field}' is not an array"

/-- A decimal integer string, the schema's endpoint encoding. -/
def decodeIntString (s : String) : Except String Int :=
  match s.toInt? with
  | some i => pure i
  | none => throw s!"'{s}' is not a decimal integer"

partial def decodeExpr (j : Json) : Except String JsExpr := do
  match ← getStr j "kind" with
  | "num" => pure (.num (← getStr j "lit"))
  | "id" => pure (.id (← getStr j "name"))
  | "unop" =>
    pure (.unop (← getStr j "op")
      (← decodeExpr (← j.getObjVal? "operand")))
  | "binop" =>
    pure (.binop (← getStr j "op")
      (← decodeExpr (← j.getObjVal? "left"))
      (← decodeExpr (← j.getObjVal? "right")))
  | "same-value" =>
    pure (.sameValue (← decodeExpr (← j.getObjVal? "left"))
      (← decodeExpr (← j.getObjVal? "right")))
  | "math-sqrt" =>
    pure (.mathSqrt (← decodeExpr (← j.getObjVal? "arg")))
  | "math-abs" =>
    pure (.mathAbs (← decodeExpr (← j.getObjVal? "arg")))
  | "number-is-finite" =>
    pure (.numberIsFinite (← decodeExpr (← j.getObjVal? "arg")))
  | "number-is-nan" =>
    pure (.numberIsNaN (← decodeExpr (← j.getObjVal? "arg")))
  | "call" =>
    pure (.call (← getStr j "callee") (← getStrOpt j "module")
      (← (← getArr j "args").mapM decodeExpr))
  | "new" =>
    pure (.newObj (← getStr j "className") (← getStrOpt j "module")
      (← (← getArr j "args").mapM decodeExpr))
  | "getter-read" =>
    pure (.getterRead (← getStr j "className") (← getStrOpt j "module")
      (← getStr j "name") (← decodeExpr (← j.getObjVal? "object")))
  | "field-read" =>
    pure (.fieldRead (← getStr j "className") (← getStrOpt j "module")
      (← getStr j "field") (← decodeExpr (← j.getObjVal? "object")))
  | "method-call" =>
    pure (.methodCall (← getStr j "className") (← getStrOpt j "module")
      (← getStr j "name") (← decodeExpr (← j.getObjVal? "object"))
      (← (← getArr j "args").mapM decodeExpr))
  | "self" => pure .selfRef
  | k => throw s!"unknown expression kind '{k}'"

partial def decodeStmt (j : Json) : Except String JsStmt := do
  match ← getStr j "kind" with
  | "return" => pure (.ret (← decodeExpr (← j.getObjVal? "expr")))
  | "throw" => pure (.throwErr (← getStr j "error"))
  | "const" =>
    pure (.constDecl (← getStr j "name")
      (← decodeExpr (← j.getObjVal? "init")))
  | "let" =>
    pure (.letDecl (← getStr j "name")
      (← decodeExpr (← j.getObjVal? "init")))
  | "assign" =>
    pure (.assign (← getStr j "name")
      (← decodeExpr (← j.getObjVal? "expr")))
  | "if" => do
    let cond ← decodeExpr (← j.getObjVal? "cond")
    let thn ← (← getArr j "then").mapM decodeStmt
    -- `else` is genuinely optional: absent means control falls through.
    let els ← match j.getObjVal? "else" with
      | .error _ => pure none
      | .ok v =>
        match v.getArr? with
        | .ok a => some <$> a.mapM decodeStmt
        | .error _ => throw "field 'else' is not an array"
    pure (.ite cond thn els)
  | "field-set" =>
    pure (.fieldSet (← getStr j "field")
      (← decodeExpr (← j.getObjVal? "expr")))
  | k => throw s!"unknown statement kind '{k}'"

/-- An array field of plain strings — names, which the schema constrains
and the renderer checks again before it emits them. -/
def decodeNames (j : Json) (field what : String) :
    Except String (Array String) := do
  (← getArr j field).mapM fun n =>
    n.getStr?.mapError fun _ => s!"a {what} is not a string"

/-- A parameter's type: the string "number", or a class object. -/
def decodeParamTy (j : Json) : Except String ParamTy :=
  match j.getStr? with
  | .ok "number" => pure .number
  | .ok s => throw s!"unknown parameter type '{s}'"
  | .error _ => do pure (.cls (← getStr j "class") (← getStrOpt j "module"))

def decodeParam (j : Json) : Except String Param := do
  pure { name := ← getStr j "name"
         ty := ← decodeParamTy (← j.getObjVal? "type") }

def decodeParams (j : Json) (field : String) : Except String (Array Param) := do
  (← getArr j field).mapM fun p =>
    (decodeParam p).mapError fun m => s!"field '{field}': {m}"

def decodeFn (j : Json) : Except String EmitFn := do
  pure { name := ← getStr j "name"
         module := ← getStrOpt j "module"
         params := ← decodeParams j "params"
         source := ← getStr j "source"
         body := ← (← getArr j "body").mapM decodeStmt }

def decodeGetter (j : Json) : Except String EmitGetter := do
  pure { name := ← getStr j "name"
         body := ← (← getArr j "body").mapM decodeStmt }

def decodeMethod (j : Json) : Except String EmitMethod := do
  pure { name := ← getStr j "name"
         params := ← decodeParams j "params"
         body := ← (← getArr j "body").mapM decodeStmt }

def decodeClass (j : Json) : Except String EmitClass := do
  -- Fields are read in schema order, so the error names the first one
  -- the object is actually missing.
  let name ← getStr j "name"
  let module ← getStrOpt j "module"
  let source ← getStr j "source"
  let fields ← decodeNames j "fields" "field name"
  let ctor ← j.getObjVal? "ctor"
  pure { name, module, source, fields
         ctorParams := ← decodeParams ctor "params"
         ctorBody := ← (← getArr ctor "body").mapM decodeStmt
         getters := ← (← getArr j "getters").mapM decodeGetter
         methods := ← (← getArr j "methods").mapM decodeMethod }

def decodeDecl (j : Json) : Except String Decl := do
  match ← getStr j "kind" with
  | "function" => .fn <$> decodeFn j
  | "class" => .cls <$> decodeClass j
  | k => throw s!"unknown declaration kind '{k}'"

/-- One side of a `number` binder's interval, absent when unbounded: an
absent side is a missing field, never a null. -/
def decodeBound (j : Json) (field : String) :
    Except String (Option (String × String)) := do
  match j.getObjVal? field with
  | .error _ => pure none
  | .ok v => pure (some (← getStr v "op", ← getStr v "lit"))

def decodeBinder (j : Json) : Except String BinderIR := do
  let name ← getStr j "name"
  match ← getStr j "kind" with
  | "range" =>
    pure (.range name (← decodeIntString (← getStr j "lo"))
      (← decodeIntString (← getStr j "hi")))
  | "int" => pure (.int name)
  | "nat" => pure (.nat name)
  | "number" =>
    pure (.number name (← decodeBound j "lower") (← decodeBound j "upper"))
  | "class" =>
    let params ← (← getArr j "ctorParams").mapM fun v =>
      match v.getStr? with
      | .ok s => pure s
      | .error _ => throw "field 'ctorParams' holds a non-string"
    pure (.cls name (← getStr j "className") (← getStrOpt j "module") params)
  | k => throw s!"unknown binder kind '{k}'"

def decodeConclusion (j : Json) : Except String Conclusion := do
  match ← getStr j "kind" with
  | "eq" =>
    pure (.eq (← decodeExpr (← j.getObjVal? "left"))
      (← decodeExpr (← j.getObjVal? "right")))
  | "istrue" => pure (.istrue (← decodeExpr (← j.getObjVal? "expr")))
  | k => throw s!"unknown conclusion kind '{k}'"

def decodePayload (j : Json) : Except String Payload := do
  match ← getStr j "kind" with
  | "structured" =>
    -- `guards` is absent, never empty, when the formula has none.
    let guards ← match j.getObjVal? "guards" with
      | .error _ => pure #[]
      | .ok v =>
        match v.getArr? with
        | .ok a => (a.mapM decodeExpr).mapError fun m => s!"field 'guards': {m}"
        | .error _ => throw "field 'guards' is not an array"
    pure (.structured (← (← getArr j "binders").mapM decodeBinder) guards
      (← decodeConclusion (← j.getObjVal? "conclusion")))
  | "bare" => pure .bare
  | k => throw s!"unknown payload kind '{k}'"

def decodeObligation (j : Json) : Except String Obligation := do
  pure { function := ← getStr j "function"
         property := ← getStr j "property"
         formula := ← getStr j "formula"
         payload := ← decodePayload (← j.getObjVal? "payload") }

/-- Decode one emission, strictly. Errors name the field or kind that
broke the schema contract. -/
def decodeEmission (j : Json) : Except String Emission := do
  pure { file := ← getStr j "file"
         declarations := ← (← getArr j "declarations").mapM decodeDecl
         obligations := ← (← getArr j "obligations").mapM decodeObligation }

end ThalesEmit
