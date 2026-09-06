import Lean

/-! Printer overrides for the artifact. -/

namespace ThalesEmit

open Lean Parser PrettyPrinter

/-- `doReturn` is `"return" >> optional (ppSpace >> checkLineEq >> term)`:
the printer may break after `return`, the parser accepts an argument only
on the same line, so a wide argument would print as a bare `return`. The
builtin formatter with a hard space in that one position. -/
@[formatter Lean.Parser.Term.doReturn]
def doReturnFormatter : Formatter :=
  withCache.formatter `Lean.Parser.Term.doReturn
    (Formatter.withAntiquot.formatter (mkAntiquot.formatter "doReturn" `Lean.Parser.Term.doReturn)
      (leadingNode.formatter `Lean.Parser.Term.doReturn leadPrec
        (withPosition.formatter
          (Formatter.andthen.formatter (symbol.formatter "return")
            (optional.formatter
              (Formatter.andthen.formatter ppHardSpace.formatter
                (Formatter.andthen.formatter Formatter.checkLineEq.formatter
                  termParser.formatter)))))))

end ThalesEmit
