import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K) [hKG : K.Normal] [hHKchar : (comap (Subgroup.subtype K) H).Characteristic] : H.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_8a {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : H ≤ K) [hHK1 : (H.subgroupOf K).Characteristic] [hK : K.Normal] :
  H.Normal := by
  letI : (comap (Subgroup.subtype K) H).Characteristic := by
    simpa only [Subgroup.comap_subtype] using hHK1
  exact dummy_assumed hHK
