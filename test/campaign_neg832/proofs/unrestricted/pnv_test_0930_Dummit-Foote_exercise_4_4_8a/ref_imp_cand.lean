import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_4_8a_assumed {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : H ≤ K) [hHK1 : (H.subgroupOf K).Characteristic] [hK : K.Normal] :
  H.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (G : Type*) [Group G] (H K : Subgroup G) (h : H ≤ K) (hK_normal : (normalizer H : Subgroup G) ≤ K) (hH_normal : normalizer H = H) : (normalizer H : Subgroup G) ≤ normalizer K := by
  rw [hH_normal]
  exact h.trans K.le_normalizer
