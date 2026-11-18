import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (H K : Subgroup G) (h : H ≤ K) (hK_normal : (normalizer H : Subgroup G) ≤ K) (hH_normal : normalizer H = H) : (normalizer H : Subgroup G) ≤ normalizer K := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_8a {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : H ≤ K) [hHK1 : (H.subgroupOf K).Characteristic] [hK : K.Normal] :
  H.Normal := by
  have htransport : (normalizer (⊤ : Subgroup K) : Subgroup K) ≤ normalizer ⊤ :=
    dummy_assumed K ⊤ ⊤ le_rfl le_top (normalizer_eq_top ⊤)
  letI hK' : K.Normal := (fun _ => hK) htransport
  rw [← Subgroup.map_subgroupOf_eq_of_le hHK]
  exact ConjAct.normal_of_characteristic_of_normal
