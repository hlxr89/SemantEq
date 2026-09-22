import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (hG : IsSolvable G) (N : Subgroup G) (hN : Normal N) : IsSolvable (G ⧸ N) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_4_5b {G : Type*} [Group G] [IsSolvable G]
  (H : Subgroup G) [Normal H] :
  IsSolvable (G ⧸ H) := by
  exact dummy_assumed (inferInstance : IsSolvable G) H (inferInstance : Normal H)
