import Lean

/-!
# `inductive` and the mathlib `Type*` notation

The `inductive` command interacts badly with `Type*`.
Universe parameters that came from the `variable` command were forgotten,
leading to parameters coming from the binder list shadowing them.
-/

elab "Type*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Lean.Elab.Term.levelMVarToParam (.sort (.succ u))

section
variable {F : Type*}

/-!
There should be three distinct level parameters.
-/
inductive I1 (A B : Type*) (x : F) : Type
/-- info: I1.{u_1, u_2, u_3} {F : Type u_1} (A : Type u_2) (B : Type u_3) (x : F) : Type -/
#guard_msgs in #check I1

/-!
This was also a problem for `axiom`.
-/
axiom ax1 (A B : Type*) (x : F) : Type
/-- info: ax1.{u_1, u_2, u_3} {F : Type u_1} (A : Type u_2) (B : Type u_3) (x : F) : Type -/
#guard_msgs in #check ax1
end
