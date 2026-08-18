import Lake
open Lake DSL

package «thales» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «ThalesDsl» where
  globs := #[.submodules `ThalesDsl, .one `ThalesDsl]

lean_lib «ThalesDslTest» where
  globs := #[.submodules `Test]
