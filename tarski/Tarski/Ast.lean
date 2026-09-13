/-! The abstract syntax of the evaluated fragment.

Every constructor names the ESTree node it decodes from, so this file,
`Tarski/Decode.lean`, and `schemas/tarski-estree.schema.json` can be read
against one another. A node kind outside this file is not a runtime
error: `Decode` refuses it as `unsupported`, and that is the only place
the word appears.

Strict mode only. Parameters are plain identifiers: a default is #393's,
rest and binding patterns are #394's, and `var` is still absent, so
hoisting here is per-block and covers `let`, `const`, and function
declarations only. `throw` and `try`, labels, and `break`/`continue` are
here; `switch` — the other breakable statement — is #393's and `for` and
`do`/`while` are #383's, classes #384's. Later slices add constructors;
they do not reshape the ones here. -/

namespace Tarski

/-- The declaration forms this slice has. `var` is deliberately absent:
hoisting and function-scoped bindings are #393's. -/
inductive DeclKind where
  /-- ESTree `VariableDeclaration` with `kind: "let"`. -/
  | «let»
  /-- ESTree `VariableDeclaration` with `kind: "const"`. -/
  | «const»
deriving Repr, DecidableEq, Inhabited

/-- The prefix operators. -/
inductive UnaryOp where
  /-- ESTree `UnaryExpression` with `operator: "-"`. -/
  | neg
  /-- ESTree `UnaryExpression` with `operator: "+"`. -/
  | plus
  /-- ESTree `UnaryExpression` with `operator: "!"`. -/
  | not
  /-- ESTree `UnaryExpression` with `operator: "typeof"`. Alone among
  these it never coerces its operand, and it is the one prefix operator
  an unresolvable identifier does not throw under: `typeof nope` is
  `"undefined"` where `nope` alone is a `ReferenceError`. -/
  | typeof
deriving Repr, DecidableEq, Inhabited

/-- The infix operators: the arithmetic four plus `%`, the four
relations, and the two strict-equality tests. Loose `==` is absent — it
coerces both operands by rules this slice does not model. -/
inductive BinaryOp where
  /-- `+`. Concatenation when either operand is a string, numeric
  addition otherwise. -/
  | add
  /-- `-`. -/
  | sub
  /-- `*`. -/
  | mul
  /-- `/`. -/
  | div
  /-- `%`. -/
  | rem
  /-- `<`. Code-point string order when both operands are strings,
  numeric otherwise. -/
  | lt
  /-- `<=`. String order on two strings, numeric otherwise. -/
  | le
  /-- `>`. String order on two strings, numeric otherwise. -/
  | gt
  /-- `>=`. String order on two strings, numeric otherwise. -/
  | ge
  /-- `===`. -/
  | strictEq
  /-- `!==`. -/
  | strictNe
  /-- `instanceof`. Neither operand is coerced: the left is compared
  against a prototype chain by identity, and the right must be a
  function. `in` is the other relational operator ESTree spells as a
  `BinaryExpression`, and it is not here. -/
  | instanceof
deriving Repr, DecidableEq, Inhabited

/-- The short-circuiting infix operators. They are not `BinaryOp`
because they do not evaluate both operands, let alone coerce them: the
value of `a && b` is one of the two operands, not a boolean. `??` is
absent — it is nullish-specific and arrives with optional chaining. -/
inductive LogicalOp where
  /-- `&&`. -/
  | and
  /-- `||`. -/
  | or
deriving Repr, DecidableEq, Inhabited

/-- Whether an operator coerces its operands before comparing them. The
two strict-equality tests do not: they answer on the values themselves,
so an object operand is not run through ToPrimitive. Neither does
`instanceof`, which is about references and has a dispatch of its own. -/
def BinaryOp.coerces : BinaryOp → Bool
  | .strictEq | .strictNe | .instanceof => false
  | _ => true

mutual

/-- Expressions. `undefLit` has no ESTree node of its own: `undefined` is
an `Identifier` there, and the decoder reads it as this literal, which is
what a strict-mode script's non-writable global binding means. -/
inductive Expr where
  /-- ESTree `Literal` with a number value. -/
  | numLit (value : Float)
  /-- ESTree `Literal` with a string value. -/
  | strLit (value : String)
  /-- ESTree `Literal` with a boolean value. -/
  | boolLit (value : Bool)
  /-- ESTree `Identifier` named `undefined`. -/
  | undefLit
  /-- ESTree `Literal` with a null value. -/
  | nullLit
  /-- ESTree `Identifier`. -/
  | ident (name : String)
  /-- ESTree `ThisExpression`. -/
  | this
  /-- ESTree `UnaryExpression`. -/
  | unary (op : UnaryOp) (operand : Expr)
  /-- ESTree `BinaryExpression`. -/
  | binary (op : BinaryOp) (left right : Expr)
  /-- ESTree `LogicalExpression`. The right operand runs only when the
  left does not already decide the answer. -/
  | logical (op : LogicalOp) (left right : Expr)
  /-- ESTree `ConditionalExpression`. -/
  | cond (test consequent alternate : Expr)
  /-- ESTree `MemberExpression` with `computed: false`. -/
  | member (object : Expr) (name : String)
  /-- ESTree `MemberExpression` with `computed: true`. The key is an
  expression, converted with ToPropertyKey when the access runs. -/
  | index (object : Expr) (key : Expr)
  /-- ESTree `CallExpression`. A `member` or `index` callee passes its
  object as the receiver; any other callee passes `undefined`. -/
  | call (callee : Expr) (args : List Expr)
  /-- ESTree `NewExpression`. -/
  | new (callee : Expr) (args : List Expr)
  /-- ESTree `ArrayExpression`. A hole and a spread are both outside the
  slice and arrive as `Unsupported` elements in place — `OmittedExpression`
  and `SpreadElement` — so the literal survives and only the element is
  refused; evaluated holes and spread are #394's. -/
  | arrayLit (elements : List Expr)
  /-- ESTree `ObjectExpression` whose members are all `kind: "init"`
  `Property` nodes with identifier or string keys, in source order.
  Shorthand, methods, accessors, computed keys, and spread are #395's. -/
  | objectLit (props : List (String × Expr))
  /-- ESTree `FunctionExpression`. A name binds only inside the
  function's own scope, which is what lets an anonymous-looking
  expression recurse. -/
  | funcExpr (name : Option String) (params : List String) (body : List Stmt)
  /-- ESTree `ArrowFunctionExpression`. An arrow has no `this` of its
  own, so `this` inside one is an ordinary lexical lookup. -/
  | arrow (params : List String) (body : ArrowBody)
  /-- ESTree `AssignmentExpression` with `operator: "="`; compound
  assignment is #383's. -/
  | assign (target : Target) (value : Expr)

/-- An arrow function's body: `expression: true` in ESTree means the
concise form, whose value is the expression's. -/
inductive ArrowBody where
  /-- The concise body: `x => x + 1`. -/
  | expr (value : Expr)
  /-- The block body: `x => { return x + 1; }`. -/
  | block (body : List Stmt)

/-- What an assignment writes to. An inductive rather than three
constructors of `Expr`, so that #383's compound assignment adds
operators and not target forms. -/
inductive Target where
  /-- ESTree `Identifier`. -/
  | ident (name : String)
  /-- ESTree `MemberExpression` with `computed: false`. -/
  | member (object : Expr) (name : String)
  /-- ESTree `MemberExpression` with `computed: true`. -/
  | index (object : Expr) (key : Expr)

/-- Statements. -/
inductive Stmt where
  /-- ESTree `ExpressionStatement`. -/
  | exprStmt (value : Expr)
  /-- ESTree `VariableDeclaration`. -/
  | varDecl (kind : DeclKind) (declarators : List Declarator)
  /-- ESTree `FunctionDeclaration`. Hoisted to the top of the block that
  contains it, and initialized there, so it may be called before its
  text and two of them may call each other. -/
  | funcDecl (name : String) (params : List String) (body : List Stmt)
  /-- ESTree `ReturnStatement`; `none` returns `undefined`. -/
  | returnStmt (argument : Option Expr)
  /-- ESTree `IfStatement`; `alternate` is the `else` arm. -/
  | ifStmt (test : Expr) (consequent : Stmt) (alternate : Option Stmt)
  /-- ESTree `WhileStatement`. -/
  | whileStmt (test : Expr) (body : Stmt)
  /-- ESTree `BlockStatement`: its own declarative scope. -/
  | block (body : List Stmt)
  /-- ESTree `ThrowStatement`. -/
  | throwStmt (argument : Expr)
  /-- ESTree `TryStatement`. `handler` is the `CatchClause` and
  `finalizer` the `finally` block's statements; at least one of the two
  is present, which the decoder enforces because `try { }` alone does not
  parse. -/
  | tryStmt (block : List Stmt) (handler : Option CatchClause)
      (finalizer : Option (List Stmt))
  /-- ESTree `LabeledStatement`. A label is not a scope: it is a target,
  and the statement it names is evaluated with the label set that reaches
  it, which is what lets a `continue` name a loop from inside a nested
  one. -/
  | labeled (label : String) (body : Stmt)
  /-- ESTree `BreakStatement`; `none` is the unlabelled form, which the
  innermost loop catches. -/
  | breakStmt (label : Option String)
  /-- ESTree `ContinueStatement`; `none` is the unlabelled form. -/
  | continueStmt (label : Option String)

/-- ESTree `CatchClause`. `param` is `none` for the optional-binding
form, `catch { }`; a binding pattern is #394's and arrives as
`Unsupported`, so the clause survives and only the binding is refused.
The parameter is a mutable binding in a scope of its own, holding nothing
but itself, which is why it does not collide with a same-named binding
outside. -/
structure CatchClause where
  /-- ESTree `CatchClause.param`, an `Identifier` or nothing. -/
  param : Option String
  /-- ESTree `CatchClause.body`, a `BlockStatement`'s statements. -/
  body : List Stmt

/-- One declarator of a `VariableDeclaration`. `none` binds `undefined`.
JS requires an initializer on a `const`, but as an early error, and early
errors are outside this epic — so `const x;` binds `undefined` here where
an engine refuses the script. -/
structure Declarator where
  /-- ESTree `VariableDeclarator.id`, an `Identifier`. -/
  name : String
  /-- ESTree `VariableDeclarator.init`. -/
  init : Option Expr

end

-- `Expr` and friends nest each other under `List` and
-- `List (String × Expr)`, which the `deriving` clause of a `mutual`
-- block does not handle; the standalone command does. `DecidableEq` is
-- not among them — no handler accepts the nesting, and nothing needs a
-- decision procedure on syntax: the tests compare programs by `repr` and
-- results by `Value`, which stays decidable.
deriving instance Repr, Inhabited for Expr, ArrowBody, Target, Stmt, CatchClause, Declarator

/-- ESTree `Program` with `sourceType: "script"`, its `"use strict"`
directive already consumed by the decoder. -/
abbrev Program := List Stmt

end Tarski
