/-! The abstract syntax of the evaluated fragment.

Every constructor names the ESTree node it decodes from, so this file,
`Tarski/Decode.lean`, and `schemas/tarski-estree.schema.json` can be read
against one another. A node kind outside this file is not a runtime
error: `Decode` refuses it as `unsupported`, and that is the only place
the word appears.

Strict mode only. Parameters are plain identifiers: a default is #393's,
rest and binding patterns are #394's. `var` is here, so hoisting covers
two scopes at once: `let`, `const`, and function declarations are
instantiated per block, while a `var` is hoisted to the enclosing
function or script and initialized to `undefined` there, with no dead
zone. `throw` and `try`, labels, `break`/`continue`, `for`, and `switch`
— the two remaining breakable statements — are here; `do`/`while`,
`for`-`in`, `arguments`, and parameter defaults are #393's, `for`-`of`
and binding patterns #394's, classes #384's. Later slices add
constructors; they do not reshape the ones here. -/

namespace Tarski

/-- The declaration forms this slice has. -/
inductive DeclKind where
  /-- ESTree `VariableDeclaration` with `kind: "let"`. -/
  | «let»
  /-- ESTree `VariableDeclaration` with `kind: "const"`. -/
  | «const»
  /-- ESTree `VariableDeclaration` with `kind: "var"`. Function-scoped
  rather than block-scoped, and hoisted: the binding is created and set
  to `undefined` when the function or script is instantiated, so a read
  before the declarator is `undefined` rather than the dead zone's
  `ReferenceError`. See `varNames` in `Tarski/Eval.lean`. -/
  | «var»
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
  /-- ESTree `UnaryExpression` with `operator: "void"`. It evaluates its
  operand — for the effects — and answers `undefined`; the value is never
  coerced, so `void {}` does not run ToPrimitive. `delete` and `~` are
  the other two spellings ESTree puts here, and neither is in the
  slice. -/
  | void
deriving Repr, DecidableEq, Inhabited

/-- The two update operators, which read a target, add or subtract one,
and write it back. ESTree gives them a node of their own, because the
value of the expression depends on which side the operator was on. -/
inductive UpdateOp where
  /-- `++`. -/
  | inc
  /-- `--`. -/
  | dec
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
  /-- `**`. ESTree spells it as a `BinaryExpression` like the rest; its
  right-associativity is the parser's business and is already resolved by
  the time the tree arrives. The meaning is `Number::exponentiate`, which
  is the library's `tsPow` — the same definition `Math.pow` has. Named
  `exponent` because `.exp` and `.pow` are spellings the arithmetic
  boundary check bans. -/
  | exponent
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
  /-- ESTree `AssignmentExpression` with `operator: "="`. -/
  | assign (target : Target) (value : Expr)
  /-- ESTree `AssignmentExpression` with one of the five arithmetic
  compound operators, `+= -= *= /= %=`, carried here as the `BinaryOp`
  they apply. The decoder refuses every other compound spelling by name:
  `**=` is not mapped onto `BinaryOp.exponent` yet, and the shifts and
  the bitwise and logical assignments need ToInt32 or short-circuiting,
  which are later slices. -/
  | compoundAssign (op : BinaryOp) (target : Target) (value : Expr)
  /-- ESTree `UpdateExpression`. `isPrefix` is ESTree's `prefix`: the
  prefix form answers the new number, the postfix form the old one, and
  both coerce the target's value with ToNumber before stepping it. -/
  | update (op : UpdateOp) (isPrefix : Bool) (target : Target)

/-- An arrow function's body: `expression: true` in ESTree means the
concise form, whose value is the expression's. -/
inductive ArrowBody where
  /-- The concise body: `x => x + 1`. -/
  | expr (value : Expr)
  /-- The block body: `x => { return x + 1; }`. -/
  | block (body : List Stmt)

/-- What an assignment writes to. An inductive rather than three
constructors of `Expr`, which is what let compound assignment and the
update operators add operators and not target forms. -/
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
  /-- ESTree `ForStatement`. The head's three parts are each optional,
  so `for (;;)` is three `none`s. A `let` head gets a fresh binding per
  iteration — copied after the body and before the update, so a closure
  the body made keeps that iteration's value — while a `const` or `var`
  head does not. -/
  | forStmt (init : Option ForInit) (test : Option Expr) (update : Option Expr)
      (body : Stmt)
  /-- ESTree `SwitchStatement`. The whole case block is one declarative
  scope, instantiated before any test runs; selection is strict equality
  in source order, a selected clause falls through into the ones after
  it, and `default` may sit anywhere among them. -/
  | switchStmt (discriminant : Expr) (cases : List SwitchCase)
  /-- ESTree `EmptyStatement`, the bare `;`. It completes empty, so it
  leaves the running completion value standing. -/
  | empty
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

/-- ESTree `ForStatement.init`: a declaration, an expression evaluated
for its effect, or nothing. A declaration head is its own scope — the
loop's — which is why the loop, and not the block around it, allocates
the cells. -/
inductive ForInit where
  /-- A `VariableDeclaration` in the head. -/
  | decl (kind : DeclKind) (declarators : List Declarator)
  /-- An expression in the head, whose value is dropped. -/
  | expr (value : Expr)

/-- ESTree `SwitchCase`. `test` is `none` for the `default` clause, and
`body` is the clause's `consequent` — the statements between this label
and the next one, which are not a block and not a scope of their own. -/
structure SwitchCase where
  /-- ESTree `SwitchCase.test`; `none` is `default`. -/
  test : Option Expr
  /-- ESTree `SwitchCase.consequent`. -/
  body : List Stmt

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
deriving instance Repr, Inhabited for Expr, ArrowBody, Target, Stmt, ForInit, SwitchCase,
  CatchClause, Declarator

/-- ESTree `Program` with `sourceType: "script"`, its `"use strict"`
directive already consumed by the decoder. -/
abbrev Program := List Stmt

end Tarski
