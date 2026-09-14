import Js
-- An artifact spells `Tarski.Program` for a declaration's ast def, and an
-- artifact imports nothing but `ThalesDsl`. Importing the AST here makes
-- `lake build`'s default target what guarantees the olean exists before
-- `lake env lean` runs an artifact, rather than `lake build thales-emit`
-- having produced it as a side effect.
import Tarski.Ast
-- An artifact's correspondence obligation spells `Tarski.project`,
-- `Tarski.readNumber`, `Tarski.runScript` and `Tarski.Outcome`, so the
-- projection rides in on the same reasoning as the AST above.
import Tarski.Project
import ThalesDsl.Verdict
import ThalesDsl.Prove
import ThalesDsl.ProveTerm
import ThalesDsl.Validate
