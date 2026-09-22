import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {H : Subgroup G} (hG : IsSolvable G) (hH : H.Normal) : IsSolvable (G ⧸ H) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_4_5b {G : Type*} [Group G] [IsSolvable G]
  (H : Subgroup G) [Normal H] :
  IsSolvable (G ⧸ H) := by
  exact dummy_assumed (H := H) (by infer_instance) (by infer_instance)
