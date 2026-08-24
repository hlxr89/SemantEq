/-
Gold reference statement (verbatim from ProofNet#, Dummit-Foote.exercise_3_1_3a, Mathlib API migrated);
theorem renamed `exercise_3_1_3a_refs`, proof replaced by `sorry`.
-/
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

/-- Let $A$ be an abelian group and let $B$ be a subgroup of $A$. Prove that $A / B$ is abelian. -/
theorem exercise_3_1_3a_refs {A : Type*} [CommGroup A] (B : Subgroup A) :
  ∀ a b : A ⧸ B, a*b = b*a :=
sorry
