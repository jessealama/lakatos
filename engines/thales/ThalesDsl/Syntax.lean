import Lean

namespace ThalesDsl

/-! The core-constructor grammar: a small, fixed surface mirroring tsc AST
node shapes. The front end pretty-prints tsc's AST into this nearly 1:1;
"accept all TypeScript" is its job, not this grammar's. Meaning lives in
the elab rules, so an unknown operator or a missing model is an
elaboration failure, never a parse failure. -/

/-- Integer literals in constructor arguments (interval endpoints, ts.num). -/
syntax tsIntLit := ("-")? num

declare_syntax_cat ts_type
syntax "ts.number" : ts_type

declare_syntax_cat ts_expr
syntax "ts.num[" tsIntLit "]" : ts_expr
syntax "ts.id[" str "]" : ts_expr
syntax "ts.binop[" str "](" ts_expr ", " ts_expr ")" : ts_expr
syntax "ts.call[" str "](" ts_expr,* ")" : ts_expr

declare_syntax_cat ts_stmt
syntax "ts.return(" ts_expr ")" : ts_stmt

/-! Graceful degradation: a construct the front end cannot map arrives as an
opaque node carrying the tsc SyntaxKind name and the construct's line and
column in the original `.ts` source. Elaborating an opaque node always
fails, so `ts_def` degrades the enclosing declaration alone. The rules are
named so failure containment can locate opaque nodes by kind. -/
syntax (name := tsOpaqueExpr) "ts.opaque[" str "](" num ", " num ")" : ts_expr
syntax (name := tsOpaqueStmt) "ts.opaque[" str "](" num ", " num ")" : ts_stmt

declare_syntax_cat ts_param
syntax "ts.param[" str "](" ts_type ")" : ts_param

/-- Declares a TS function model: elaborates the body into a Lean
definition under `TsModel.*` and registers it by its TS name. -/
syntax "ts_def " str " := " "ts.fn(" ts_param,* ")" " : " ts_type " {" ts_stmt* "}" : command

/-- A whole declaration the front end could not shape as `ts.fn` — a class
member, a const-arrow, an inexpressible signature. Elaborating it records
the name as failed with the unmapped construct, so its annotations degrade
to `Inappropriate`. -/
syntax "ts_def " str " := " "ts.opaque[" str "](" num ", " num ")" : command

/-! Property constructors for the Lemma prefix/formula shapes this slice
supports: bounded ∀-binders over int ranges and unbounded int/nat binders,
`≡` equations between value islands, and boolean islands. -/

declare_syntax_cat ts_binder
syntax "ts.binder[" str "](" "ts.int" ", " "ts.range(" tsIntLit ", " tsIntLit ")" ")" : ts_binder
syntax "ts.binder[" str "](" "ts.int" ")" : ts_binder
syntax "ts.binder[" str "](" "ts.nat" ")" : ts_binder

declare_syntax_cat ts_prop
syntax "ts.eq(" ts_expr ", " ts_expr ")" : ts_prop
syntax "ts.istrue(" ts_expr ")" : ts_prop
syntax "ts.forall(" ts_binder,* ")" " {" ts_prop "}" : ts_prop

/-- States a per-annotation proof obligation and reports its verdict as one
JSON line on stdout. Without a structured property the command is a stub
reporting `NotTried`. -/
syntax "#thales_prove " str str str (" := " ts_prop)? : command

end ThalesDsl
