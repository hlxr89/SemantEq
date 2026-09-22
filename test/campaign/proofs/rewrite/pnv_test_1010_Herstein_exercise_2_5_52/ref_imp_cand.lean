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
theorem dummy {G : Type*} [Fintype G] [Group G] (φ : G ≃* G) (hφ : ∃ S : Finset G, S.card > (3 * Fintype.card G) / 4 ∧ ∀ x ∈ S, φ x = x⁻¹) : (∀ y : G, φ y = y⁻¹) ∧ (∀ a b : G, a * b = b * a) := by
  obtain ⟨S, hS, hfix⟩ := hφ
  apply exercise_2_5_52_assumed φ hfix
  have hmul : 3 * Fintype.card G < S.card * 4 :=
    (Nat.div_lt_iff_lt_mul (Nat.succ_pos 3)).mp hS
  have hmulQ : (3 : ℚ) * Fintype.card G < S.card * 4 := by
    exact_mod_cast hmul
  have hdecimal : (0.75 : ℚ) = 3 / 4 := by
    rw [← Rat.ofScientific_eq_ofScientific, Rat.ofScientific_true_def,
      Rat.mkRat_eq_div]
    change (75 : ℚ) / 100 = 3 / 4
    have h75 : (75 : ℚ) = 3 * 25 := by
      exact_mod_cast (show (75 : ℕ) = 3 * 25 by rfl)
    have h100 : (100 : ℚ) = 4 * 25 := by
      exact_mod_cast (show (100 : ℕ) = 4 * 25 by rfl)
    have h25 : (25 : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero 24)
    rw [h75, h100, mul_div_mul_right _ _ h25]
  rw [hdecimal]
  rw [Fintype.card_coe]
  rw [div_mul_eq_mul_div]
  have hfour : (0 : ℚ) < 4 := by
    exact_mod_cast (Nat.succ_pos 3)
  exact (div_le_iff₀' hfour).mpr (by
    simpa only [mul_comm] using hmulQ.le)
