import Lake
open Lake DSL

package «tarski» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Js» where
  globs := #[.submodules `Js, .one `Js]

@[default_target]
lean_lib «Tarski» where
  globs := #[.submodules `Tarski, .one `Tarski]

/-- The evaluator's binary: `tarski run <file.json>`. Nothing is
elaborated at runtime, so it needs no interpreter support. -/
@[default_target]
lean_exe «tarski» where
  root := `Tarski.Main

lean_lib «TarskiTest» where
  -- `.submodules `Test` also matches sibling Test.* trees in a workspace
  -- that requires this package, and lake then looks for those files here.
  globs := #[.submodules `Test.Js, .submodules `Test.Tarski]
