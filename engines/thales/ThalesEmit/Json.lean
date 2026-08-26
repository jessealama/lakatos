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
  | call (callee : String) (module : Option String) (args : Array JsExpr)
deriving Repr, Inhabited

inductive JsStmt where
  | ret (expr : JsExpr)
  | throwErr (error : String)
  | constDecl (name : String) (init : JsExpr)
  | letDecl (name : String) (init : JsExpr)
  | assign (name : String) (expr : JsExpr)
  | ite (cond : JsExpr) (thn : Array JsStmt) (els : Option (Array JsStmt))
deriving Repr, Inhabited

structure EmitFn where
  name : String
  /-- The defining module's entry-relative path; none for the entry. -/
  module : Option String := none
  params : Array String
  source : String
  body : Array JsStmt
deriving Repr, Inhabited

/-- A binder's denoted domain: a finite half-open `[lo, hi)` integer
range, the whole int line, the naturals, or the doubles a `number`
binder's bounds admit — each bound an op × endpoint-literal pair. -/
inductive BinderIR where
  | range (name : String) (lo hi : Int)
  | int (name : String)
  | nat (name : String)
  | number (name : String) (lower upper : Option (String × String))
deriving Repr, Inhabited

def BinderIR.name : BinderIR → String
  | .range n _ _ => n
  | .int n => n
  | .nat n => n
  | .number n _ _ => n

/-- Whether the binder enumerates `Int`s, so a use of it inside the body
crosses to the Float world. A `number` binder is already a double. -/
def BinderIR.isIntValued : BinderIR → Bool
  | .number .. => false
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
  declarations : Array EmitFn
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
  | "call" =>
    pure (.call (← getStr j "callee") (← getStrOpt j "module")
      (← (← getArr j "args").mapM decodeExpr))
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
  | k => throw s!"unknown statement kind '{k}'"

def decodeFn (j : Json) : Except String EmitFn := do
  match ← getStr j "kind" with
  | "function" =>
    pure { name := ← getStr j "name"
           module := ← getStrOpt j "module"
           params := ← (← getArr j "params").mapM fun p =>
             p.getStr?.mapError fun _ => "a parameter name is not a string"
           source := ← getStr j "source"
           body := ← (← getArr j "body").mapM decodeStmt }
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
         declarations := ← (← getArr j "declarations").mapM decodeFn
         obligations := ← (← getArr j "obligations").mapM decodeObligation }

end ThalesEmit
