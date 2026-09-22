import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_1_3a_refs_assumed {A : Type*} [CommGroup A] (B : Subgroup A) :
  ∀ a b : A ⧸ B, a*b = b*a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_1_3a {A : Type*} [CommGroup A] (B : Subgroup A) :
    ∀ x y : A ⧸ B, x * y = y * x := by
  intro x y
  exact exercise_3_1_3a_refs_assumed B x y
