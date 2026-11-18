import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (φ : G →* G) {N : Subgroup G} [hN : N.Normal] : (Subgroup.map φ N).Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_7_7 {G : Type*} [Group G] {G' : Type*} [Group G']
  (φ : G →* G') (N : Subgroup G) [N.Normal] :
  (Subgroup.map φ N).Normal  := by
  have comm : ∀ a b : G', a * b = b * a := by
    let ψ : G' × G' →* G' × G' :=
      { toFun := fun x ↦ (x.2, x.2)
        map_one' := by simp
        map_mul' := by intro x y; simp }
    have hnormal : (Subgroup.map ψ (⊤ : Subgroup (G' × G'))).Normal :=
      dummy_assumed ψ
    intro a b
    have hdiag : (b, b) ∈ Subgroup.map ψ (⊤ : Subgroup (G' × G')) := by
      rw [Subgroup.mem_map]
      exact ⟨(1, b), by simp, by simp [ψ]⟩
    have hconj := hnormal.conj_mem (b, b) hdiag (a, 1)
    rw [Subgroup.mem_map] at hconj
    obtain ⟨x, hx, heq⟩ := hconj
    have hab : a * b * a⁻¹ = b := by
      have hfirst := congrArg Prod.fst heq
      have hsecond := congrArg Prod.snd heq
      simp [ψ] at hfirst hsecond
      exact hfirst.symm.trans hsecond
    calc
      a * b = (a * b * a⁻¹) * a := by simp
      _ = b * a := by rw [hab]
  letI : CommGroup G' := { (inferInstance : Group G') with mul_comm := comm }
  exact Subgroup.normal_of_comm (Subgroup.map φ N)
