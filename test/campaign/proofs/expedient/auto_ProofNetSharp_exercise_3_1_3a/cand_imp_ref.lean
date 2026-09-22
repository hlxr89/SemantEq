import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_1_3a_assumed {A : Type*} [CommGroup A] (B : Subgroup A) :
    ∀ x y : A ⧸ B, x * y = y * x :=
  by
    sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_1_3a_refs {A : Type*} [CommGroup A] (B : Subgroup A) :
  ∀ a b : A ⧸ B, a*b = b*a := by
  intro a b
  exact mul_comm a b
