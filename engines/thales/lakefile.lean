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

lean_lib «ThalesDslTest» where
  globs := #[.submodules `Test]
