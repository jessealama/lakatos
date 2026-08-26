namespace Js

/-- The type a TypeScript `number` actually holds: IEEE-754 binary64. -/
abbrev JsNumber := Float

/-- IEEE NaN, the value the `NaN` global names (core has `Float.isNaN`
but no constant; a future toolchain's `Float.nan` can replace the body). -/
def floatNaN : Float := 0.0 / 0.0

end Js
