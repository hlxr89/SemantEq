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
theorem dummy {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K) [hKG : K.Normal] [hHKchar : (comap (Subgroup.subtype K) H).Characteristic] : H.Normal := by
  letI : (H.subgroupOf K).Characteristic := by
    simpa only [Subgroup.subgroupOf] using hHKchar
  exact exercise_4_4_8a_assumed H K hHK
