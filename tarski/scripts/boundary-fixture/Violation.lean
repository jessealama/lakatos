-- Not part of any `lean_lib` glob: the `Tarski` library is
-- `.submodules `Tarski`, and `scripts/` is outside it. This file exists
-- so CI can point `check-boundary.sh` at this directory and see it fail.
-- A check that has never refused anything is not evidence.
def bad (x : Float) : Float := Float.sqrt x
