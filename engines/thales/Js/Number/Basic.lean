namespace Js

/-- The type a TypeScript `number` actually holds: IEEE-754 binary64. -/
abbrev JsNumber := Float

/-- IEEE NaN, the value the `NaN` global names: core's constant under the
name the renderer emits as an atom. -/
def floatNaN : Float := Float.nan

end Js
