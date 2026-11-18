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
  let e : (↥(⊤ : Subgroup G)) ≃* G := Subgroup.topEquiv
  letI : (H.subgroupOf (⊤ : Subgroup G)).Characteristic :=
    { fixed := fun ϕ => by
        let ψ : G ≃* G := e.symm.trans (ϕ.trans e)
        ext x
        change (e (ϕ (e.symm (e x))) ∈ H) ↔ e x ∈ H
        simpa [ψ, e] using SetLike.ext_iff.mp (hH.fixed ψ) (e x) }
  exact exercise_4_4_8a_assumed H ⊤ le_top
