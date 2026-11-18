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
theorem dummy {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K) (hH : H.Characteristic) (hK : K.Normal) : H.Normal := by
  letI : H.Characteristic := hH
  letI : (H.subgroupOf (⊤ : Subgroup G)).Characteristic :=
    ⟨fun φ => by
      ext x
      let ψ : G ≃* G := Subgroup.topEquiv.symm.trans (φ.trans Subgroup.topEquiv)
      have hx := SetLike.ext_iff.mp (hH.fixed ψ) (x : G)
      exact hx⟩
  exact exercise_4_4_8a_assumed H ⊤ le_top
