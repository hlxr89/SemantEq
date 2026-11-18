import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K) (hH : H.Characteristic) (hK : K.Normal) : H.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_8a {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : H ≤ K) [hHK1 : (H.subgroupOf K).Characteristic] [hK : K.Normal] :
  H.Normal := by
  have hnormal : ((H.subgroupOf K).map K.subtype).Normal := inferInstance
  rw [Subgroup.map_subgroupOf_eq_of_le hHK] at hnormal
  exact hnormal
