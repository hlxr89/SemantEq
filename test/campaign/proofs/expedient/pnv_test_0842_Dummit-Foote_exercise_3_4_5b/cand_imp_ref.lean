import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal) (hG : IsSolvable G) : IsSolvable (G ⧸ N) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_4_5b {G : Type*} [Group G] [IsSolvable G]
  (H : Subgroup G) [Normal H] :
  IsSolvable (G ⧸ H) := by
  exact dummy_assumed (inferInstance : H.Normal) (inferInstance : IsSolvable G)
