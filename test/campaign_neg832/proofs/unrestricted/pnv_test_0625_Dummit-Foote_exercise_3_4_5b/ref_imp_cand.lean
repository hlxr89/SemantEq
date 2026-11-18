import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_4_5b_assumed {G : Type*} [Group G] [IsSolvable G]
  (H : Subgroup G) [Normal H] :
  IsSolvable (G ⧸ H) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (G : Type*) [Group G] (G' : Type*) [Group G'] (f : G →* G') (hf : Function.Surjective f) (h1 : IsSolvable G) : IsSolvable G' := by
  letI : IsSolvable G := h1
  exact solvable_of_surjective hf
