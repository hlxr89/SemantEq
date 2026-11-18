import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] (φ : MonoidHom G G) (t : Finset G) (ht : t.card = Fintype.card G / 4) (h : ∀ x ∈ t, φ x = x⁻¹) : ∀ x : G, φ x = x⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_5_52 {G : Type*} [Group G] [Fintype G]
  (φ : G ≃* G) {I : Finset G} (hI : ∀ x ∈ I, φ x = x⁻¹)
  (hI1 : (0.75 : ℚ) * card G ≤ card I) :
  (∀ x : G, φ x = x⁻¹) ∧ ∀ x y : G, x*y = y*x := by
  rw [Fintype.card_coe] at hI1
  have hquarter : Fintype.card G / 4 ≤ I.card := by
    have hquarterQ : ((Fintype.card G / 4 : ℕ) : ℚ) ≤ (I.card : ℚ) := by
      exact Nat.cast_div_le.trans <| (show (Fintype.card G : ℚ) / 4 ≤ (I.card : ℚ) from
        (show (Fintype.card G : ℚ) / 4 ≤ (0.75 : ℚ) * Fintype.card G by
          rw [div_eq_mul_inv, mul_comm (0.75 : ℚ)]
          exact mul_le_mul_of_nonneg_left (show (4 : ℚ)⁻¹ ≤ 0.75 by norm_num)
            (Nat.cast_nonneg _)).trans hI1)
    exact_mod_cast hquarterQ
  obtain ⟨t, htI, ht⟩ := Finset.exists_subset_card_eq hquarter
  have hinv : ∀ x : G, φ x = x⁻¹ :=
    dummy_assumed φ.toMonoidHom t ht (λ x hx ↦ hI x (htI hx))
  refine ⟨hinv, ?_⟩
  intro x y
  have hcommInv : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by
    exact (congrArg₂ (fun a b ↦ a * b) (hinv x).symm (hinv y).symm).trans <|
      (φ.map_mul x y).symm.trans <| (hinv (x * y)).trans (mul_inv_rev x y)
  have hcommInv' := congrArg Inv.inv hcommInv
  simpa only [mul_inv_rev, inv_inv] using hcommInv'.symm
