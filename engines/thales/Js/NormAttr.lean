import Lean

-- A registered simp attribute is only usable in modules that import its
-- registration, so the `js_norm` set lives one module below its lemmas.
register_simp_attr js_norm
