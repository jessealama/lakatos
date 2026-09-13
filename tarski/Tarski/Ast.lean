/-! The abstract syntax of the evaluator's first slice: numeric scripts.

Every constructor names the ESTree node it decodes from, so this file,
`Tarski/Decode.lean`, and `schemas/tarski-estree.schema.json` can be read
against one another. A node kind outside this file is not a runtime
error: `Decode` refuses it as `unsupported`, and that is the only place
the word appears.

Strict mode only, and only what a numeric script needs — no strings, no
objects, no functions, no `throw`/`try`, no `var`. Later slices add
constructors; they do not reshape the ones here. -/

namespace Tarski

/-- The declaration forms this slice has. `var` is deliberately absent:
hoisting and function-scoped bindings are #393's. -/
inductive DeclKind where
  /-- ESTree `VariableDeclaration` with `kind: "let"`. -/
  | «let»
  /-- ESTree `VariableDeclaration` with `kind: "const"`. -/
  | «const»
deriving Repr, DecidableEq, Inhabited

/-- The prefix operators over the numeric domain. `typeof` is absent: its
result is a string, and strings arrive with #380. -/
inductive UnaryOp where
  /-- ESTree `UnaryExpression` with `operator: "-"`. -/
  | neg
  /-- ESTree `UnaryExpression` with `operator: "+"`. -/
  | plus
  /-- ESTree `UnaryExpression` with `operator: "!"`. -/
  | not
deriving Repr, DecidableEq, Inhabited

/-- The infix operators over the numeric domain: the arithmetic four plus
`%`, the four relations, and the two strict-equality tests. Loose `==`
is absent — it coerces, and coercion beyond numbers is a later slice. -/
inductive BinaryOp where
  /-- `+`. Numeric addition only: no operand of this slice is a string. -/
  | add
  /-- `-`. -/
  | sub
  /-- `*`. -/
  | mul
  /-- `/`. -/
  | div
  /-- `%`. -/
  | rem
  /-- `<`. -/
  | lt
  /-- `<=`. -/
  | le
  /-- `>`. -/
  | gt
  /-- `>=`. -/
  | ge
  /-- `===`. -/
  | strictEq
  /-- `!==`. -/
  | strictNe
deriving Repr, DecidableEq, Inhabited

/-- Expressions. `undefLit` has no ESTree node of its own: `undefined` is
an `Identifier` there, and the decoder reads it as this literal, which is
what a strict-mode script's non-writable global binding means. -/
inductive Expr where
  /-- ESTree `Literal` with a number value. -/
  | numLit (value : Float)
  /-- ESTree `Literal` with a boolean value. -/
  | boolLit (value : Bool)
  /-- ESTree `Identifier` named `undefined`. -/
  | undefLit
  /-- ESTree `Literal` with a null value. -/
  | nullLit
  /-- ESTree `Identifier`. -/
  | ident (name : String)
  /-- ESTree `UnaryExpression`. -/
  | unary (op : UnaryOp) (operand : Expr)
  /-- ESTree `BinaryExpression`. -/
  | binary (op : BinaryOp) (left right : Expr)
  /-- ESTree `ConditionalExpression`. -/
  | cond (test consequent alternate : Expr)
  /-- ESTree `AssignmentExpression` with `operator: "="` and an
  `Identifier` target; compound assignment waits for a later slice. -/
  | assign (target : String) (value : Expr)
deriving Repr, DecidableEq, Inhabited

/-- One declarator of a `VariableDeclaration`. `none` binds `undefined`.
JS requires an initializer on a `const`, but as an early error, and early
errors are outside this epic — so `const x;` binds `undefined` here where
an engine refuses the script. -/
structure Declarator where
  /-- ESTree `VariableDeclarator.id`, an `Identifier`. -/
  name : String
  /-- ESTree `VariableDeclarator.init`. -/
  init : Option Expr
deriving Repr, DecidableEq, Inhabited

/-- Statements. `Stmt` nests itself under `List`, which no `DecidableEq`
deriving handler accepts; nothing needs a decision procedure on whole
statements, and the tests that compare them do it by reduction. -/
inductive Stmt where
  /-- ESTree `ExpressionStatement`. -/
  | exprStmt (value : Expr)
  /-- ESTree `VariableDeclaration`. -/
  | varDecl (kind : DeclKind) (declarators : List Declarator)
  /-- ESTree `IfStatement`; `alternate` is the `else` arm. -/
  | ifStmt (test : Expr) (consequent : Stmt) (alternate : Option Stmt)
  /-- ESTree `WhileStatement`. -/
  | whileStmt (test : Expr) (body : Stmt)
  /-- ESTree `BlockStatement`: its own declarative scope. -/
  | block (body : List Stmt)
deriving Repr, Inhabited

/-- ESTree `Program` with `sourceType: "script"`, its `"use strict"`
directive already consumed by the decoder. -/
abbrev Program := List Stmt

end Tarski
