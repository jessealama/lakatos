import Lean.Data.Json

/-! The emission IR: the shapes `schemas/thales-emission.schema.json`
fixes, decoded strictly — an unknown kind or a missing field is a decode
error naming the offender, and the whole run fails cleanly on it. -/

namespace ThalesEmit

open Lean

inductive JsExpr where
  | num (lit : String)
  | id (name : String)
  | binop (op : String) (left right : JsExpr)
  | call (callee : String) (args : Array JsExpr)
deriving Repr, Inhabited

inductive JsStmt where
  | ret (expr : JsExpr)
deriving Repr, Inhabited

structure EmitFn where
  name : String
  params : Array String
  source : String
  body : Array JsStmt
deriving Repr, Inhabited

structure BinderIR where
  name : String
  lo : Int
  hi : Int
deriving Repr, Inhabited

inductive Conclusion where
  | eq (left right : JsExpr)
  | istrue (expr : JsExpr)
deriving Repr, Inhabited

inductive Payload where
  | structured (binders : Array BinderIR) (conclusion : Conclusion)
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
  | "binop" =>
    pure (.binop (← getStr j "op")
      (← decodeExpr (← j.getObjVal? "left"))
      (← decodeExpr (← j.getObjVal? "right")))
  | "call" =>
    pure (.call (← getStr j "callee")
      (← (← getArr j "args").mapM decodeExpr))
  | k => throw s!"unknown expression kind '{k}'"

def decodeStmt (j : Json) : Except String JsStmt := do
  match ← getStr j "kind" with
  | "return" => pure (.ret (← decodeExpr (← j.getObjVal? "expr")))
  | k => throw s!"unknown statement kind '{k}'"

def decodeFn (j : Json) : Except String EmitFn := do
  match ← getStr j "kind" with
  | "function" =>
    pure { name := ← getStr j "name"
           params := ← (← getArr j "params").mapM fun p =>
             p.getStr?.mapError fun _ => "a parameter name is not a string"
           source := ← getStr j "source"
           body := ← (← getArr j "body").mapM decodeStmt }
  | k => throw s!"unknown declaration kind '{k}'"

def decodeBinder (j : Json) : Except String BinderIR := do
  pure { name := ← getStr j "name"
         lo := ← decodeIntString (← getStr j "lo")
         hi := ← decodeIntString (← getStr j "hi") }

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
    pure (.structured (← (← getArr j "binders").mapM decodeBinder)
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
