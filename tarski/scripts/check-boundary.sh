#!/bin/sh
# The evaluator's arithmetic boundary.
#
# Every arithmetic and comparison the evaluator performs must be one the
# `Js` library models, so that a `Theorem` and a run appeal to the same
# meaning. Lean's own `Float` instances *are* the library's model of
# `Number` — `JsNumber := Float` — so infix `+ - * /`, unary `-`, `==`,
# `<`, and `≤` are the sanctioned spellings and stay allowed. What is
# banned under `Tarski/` is everything else that reaches binary64
# directly: any `Float`-namespace call (`Float.sqrt`, `Float.lt`,
# `Float.ofNat`, …) and the method-syntax operations and coercions
# (`.isNaN`, `.toUInt64`, `.floor`, `.toString`, …). Anything the library
# names — `Js.Number.FloatOps.tsRem`, `Js.floatNaN`, `Js.JsVal.typeof` —
# is a `Js.` name and never matches.
#
# The boundary is about arithmetic the evaluator *performs*, so each file
# is stripped of its comments and its string-literal text before the
# pattern runs: `Error.prototype.toString` is a JavaScript method this
# file has opinions about only when Lean calls it, and the same will hold
# of `Math.round` (#382) and `Number.prototype.toString` (#388). An
# interpolated term inside `s!"…{e}…"` is code and is kept. Line numbers
# survive the stripping, so a hit still names its line.
#
# Two exemptions:
#
#   * `Tarski/Format.lean` is provisional `Number::toString`, written
#     against the runtime's own `Float.toString`. #388 replaces that file
#     with the ECMA algorithm and this exemption goes with it.
#   * The optional directory argument (default `Tarski`) lets CI point
#     the check at `scripts/boundary-fixture`, which plants a violation,
#     and so check that the check bites.
#
# Usage: sh scripts/check-boundary.sh [directory]
set -eu

root="${1:-Tarski}"
exempt="Tarski/Format.lean"

pattern='(\bFloat\.[A-Za-z]|\.(isNaN|isInf|isFinite|toU[A-Za-z0-9]*|toInt[0-9]*|floor|ceil|round|abs|sqrt|exp|log|pow|toString|toBits|frExp|scaleB)\b)'

# Blank out comments and string-literal text, keeping line numbers and
# interpolated terms.
strip='
BEGIN { depth = 0; instr = 0; interp = 0 }
{
  line = $0; n = length(line); out = ""; i = 1
  while (i <= n) {
    c = substr(line, i, 1); two = substr(line, i, 2)
    if (interp > 0) {
      if (c == "{") interp++
      else if (c == "}") interp--
      out = out c; i++; continue
    }
    if (instr) {
      if (c == "\\") { out = out "  "; i += 2; continue }
      if (c == "{") { interp = 1; out = out c; i++; continue }
      if (c == "\"") { instr = 0; out = out " "; i++; continue }
      out = out " "; i++; continue
    }
    if (depth > 0) {
      if (two == "/-") { depth++; out = out "  "; i += 2; continue }
      if (two == "-/") { depth--; out = out "  "; i += 2; continue }
      out = out " "; i++; continue
    }
    if (two == "/-") { depth++; out = out "  "; i += 2; continue }
    if (two == "--") { while (i <= n) { out = out " "; i++ }; continue }
    if (c == "\"") { instr = 1; out = out " "; i++; continue }
    out = out c; i++
  }
  print out
}
'

hits=$(mktemp)
trap 'rm -f "$hits"' EXIT

scanned=0
for file in $(find "$root" -name '*.lean' | sort); do
  if [ "$file" = "$exempt" ]; then
    continue
  fi
  scanned=$((scanned + 1))
  awk "$strip" "$file" | grep -nE "$pattern" | sed "s|^|$file:|" >>"$hits" || true
done

violations=$(wc -l <"$hits" | tr -d ' ')
if [ "$violations" -ne 0 ]; then
  cat "$hits"
  echo "boundary: $violations violation(s)"
  exit 1
fi

echo "boundary: $scanned file(s) clean"
