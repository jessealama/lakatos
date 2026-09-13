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

hits=$(mktemp)
trap 'rm -f "$hits"' EXIT

scanned=0
for file in $(find "$root" -name '*.lean' | sort); do
  if [ "$file" = "$exempt" ]; then
    continue
  fi
  scanned=$((scanned + 1))
  grep -HnE "$pattern" "$file" >>"$hits" || true
done

violations=$(wc -l <"$hits" | tr -d ' ')
if [ "$violations" -ne 0 ]; then
  cat "$hits"
  echo "boundary: $violations violation(s)"
  exit 1
fi

echo "boundary: $scanned file(s) clean"
