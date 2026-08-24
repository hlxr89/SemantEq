/-
Autoformalized from NL only (blind); benchmark: ProofNetSharp; problem: exercise_3_1_3a.
-/
import Mathlib

/-- Let $A$ be an abelian group and let $B$ be a subgroup of $A$. Prove that $A / B$ is abelian. -/
theorem exercise_3_1_3a {A : Type*} [CommGroup A] (B : Subgroup A) :
    ∀ x y : A ⧸ B, x * y = y * x :=
  sorry
