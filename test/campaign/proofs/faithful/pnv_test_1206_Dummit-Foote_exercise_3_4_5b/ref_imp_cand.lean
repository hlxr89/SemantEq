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
theorem dummy {G : Type*} [Group G] (hG : IsSolvable G) (N : Subgroup G) (hN : Normal N) : IsSolvable (G ⧸ N) := by
  letI := hG
  letI := hN
  exact exercise_3_4_5b_assumed N
