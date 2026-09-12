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

lean_lib «TarskiTest» where
  -- `.submodules `Test` also matches sibling Test.* trees in a workspace
  -- that requires this package, and lake then looks for those files here.
  globs := #[.submodules `Test.Js]
