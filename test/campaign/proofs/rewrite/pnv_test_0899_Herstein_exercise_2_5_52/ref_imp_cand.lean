import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_5_52_assumed {G : Type*} [Group G] [Fintype G]
  (φ : G ≃* G) {I : Finset G} (hI : ∀ x ∈ I, φ x = x⁻¹)
  (hI1 : (0.75 : ℚ) * card G ≤ card I) :
  (∀ x : G, φ x = x⁻¹) ∧ ∀ x y : G, x*y = y*x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] [Fintype G] (φ : G ≃* G) (hφ : ∃ S : Finset G, S.card > (3 * Fintype.card G) / 4 ∧ ∀ x ∈ S, φ x = x⁻¹) : ∀ y : G, φ y = y⁻¹ ∧ ∀ a b : G, a * b = b * a := by
  obtain ⟨S, hScard, hS⟩ := hφ
  have hNat : 3 * Fintype.card G < S.card * 4 :=
    (Nat.div_lt_iff_lt_mul (by decide)).mp hScard
  have hNat' : 3 * Fintype.card G ≤ S.card * 4 := Nat.le_of_lt hNat
  have hRat : (3 : ℚ) * Fintype.card G ≤ S.card * 4 := by
    exact_mod_cast hNat' -- non-rewrite step
  have hThreeQuarters : (0.75 : ℚ) * Fintype.card G ≤ S.card := by
    rw [show (0.75 : ℚ) = 3 / 4 by norm_num]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by decide)]
    exact hRat
  have hRefBound : (0.75 : ℚ) * Fintype.card G ≤ Fintype.card ↥S := by
    rw [Fintype.card_coe]
    exact hThreeQuarters
  obtain ⟨hInv, hComm⟩ := exercise_2_5_52_assumed φ hS hRefBound
  intro y
  exact ⟨hInv y, hComm⟩
