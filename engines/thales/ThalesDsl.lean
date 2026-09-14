import Js
-- An artifact spells `Tarski.Program` for a declaration's ast def, and an
-- artifact imports nothing but `ThalesDsl`. Importing the AST here makes
-- `lake build`'s default target what guarantees the olean exists before
-- `lake env lean` runs an artifact, rather than `lake build thales-emit`
-- having produced it as a side effect.
import Tarski.Ast
import ThalesDsl.Verdict
import ThalesDsl.Prove
import ThalesDsl.ProveTerm
