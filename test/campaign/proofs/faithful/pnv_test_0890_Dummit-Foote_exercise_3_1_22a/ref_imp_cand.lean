import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_1_22a_assumed (G : Type*) [Group G] (H K : Subgroup G)
  [Normal H] [Normal K] :
  Normal (H ⊓ K) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] {H K : Subgroup G} (hH : Normal H) (hK : Normal K) : Normal (H ⊓ K) := by
  letI : Normal H := hH
  letI : Normal K := hK
  exact exercise_3_1_22a_assumed G H K
