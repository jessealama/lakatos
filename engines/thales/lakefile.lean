import Lake
open Lake DSL

package «thales» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Js» where
  globs := #[.submodules `Js, .one `Js]

@[default_target]
lean_lib «ThalesDsl» where
  globs := #[.submodules `ThalesDsl, .one `ThalesDsl]

lean_lib «ThalesEmit» where
  globs := #[.submodules `ThalesEmit, .one `ThalesEmit]

lean_exe «thales-emit» where
  root := `ThalesEmit.Main
  -- The renderer imports ThalesDsl at runtime and pretty-prints through
  -- interpreted parenthesizers, which needs the interpreter's symbols.
  supportInterpreter := true

lean_lib «ThalesDslTest» where
  globs := #[.submodules `Test]
