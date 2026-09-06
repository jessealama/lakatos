import ThalesEmit

/-! Comparators for the rendering tests: a rendered tree against a test
quotation, with no pretty-printer in the loop. -/

open Lean ThalesEmit

/-- Macro scopes and preresolved names record the quoting context, not the
syntax, so trees from different modules compare only once both are erased.
A paren node is the parenthesizer's business: the renderer builds nested
applications bare and a quotation writes them parenthesized. -/
partial def strip : Syntax → Syntax
  | .ident info _ val _ =>
    let val := val.eraseMacroScopes
    .ident info (toString val).toRawSubstring val []
  | .node _ ``Lean.Parser.Term.paren #[_, inner, _] => strip inner
  | .node info kind args => .node info kind (args.map strip)
  | s => s

def syntaxEq (a b : Syntax) : Bool := (strip a).structEq (strip b)

def rendersSyntax {k : SyntaxNodeKinds} (x : RenderM (TSyntax k))
    (expected : Unhygienic (TSyntax k)) : Bool :=
  match RenderM.run x with
  | .ok t => syntaxEq t.raw (Unhygienic.run expected).raw
  | .error _ => false

def rendersAs (x : RenderM Rendered) (expected : Unhygienic Term) : Bool :=
  rendersSyntax (do return (← x).term) expected

/-- The term and its lift flag together. -/
def rendersLifted (x : RenderM Rendered) (lifted : Bool)
    (expected : Unhygienic Term) : Bool :=
  match RenderM.run x with
  | .ok r => r.lifted == lifted && syntaxEq r.term.raw (Unhygienic.run expected).raw
  | .error _ => false

/-- A `monadicTerm` result: the term and whether it pins `JsM`. -/
def monadicAs (x : RenderM (Term × Bool)) (pins : Bool)
    (expected : Unhygienic Term) : Bool :=
  match RenderM.run x with
  | .ok (t, p) => p == pins && syntaxEq t.raw (Unhygienic.run expected).raw
  | .error _ => false

def renderFails {α : Type} (x : RenderM α) : Bool :=
  match RenderM.run x with
  | .error _ => true
  | .ok _ => false

/-- For a failing guard: what the renderer actually built. -/
def showRendered {k : SyntaxNodeKinds} (x : RenderM (TSyntax k)) : IO Unit :=
  match RenderM.run x with
  | .ok t => IO.println (toString (strip t.raw))
  | .error msg => IO.println s!"render error: {msg}"

/-- The comparator's own controls: the operand flip is seen, a wrong
rendering is caught, and parentheses do not separate equal trees. -/
private def v (e : JsExpr) : RenderM Rendered := valueTerm (fun _ => false) e

#guard rendersAs (v (.binop ">" (.id "a") (.id "b"))) `(Float.lt b a)
#guard !rendersAs (v (.binop ">" (.id "a") (.id "b"))) `(Float.lt a b)
#guard rendersAs (v (.call "f" none #[.binop "+" (.id "a") (.num "1")]))
  `((← TsModel.f (a + 1)))
#guard rendersLifted (v (.call "f" none #[])) true `((← TsModel.f))
#guard !rendersLifted (v (.id "a")) true `(a)
#guard renderFails (v (.id "1x"))
