import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- (empty)

-- ===== assumed statement (antecedent) =====
theorem exercise_2_5_52_assumed {G : Type*} [Group G] [Fintype G]
  (φ : G ≃* G) {I : Finset G} (hI : ∀ x ∈ I, φ x = x⁻¹)
  (hI1 : (0.75 : ℚ) * card G ≤ card I) :
  (∀ x : G, φ x = x⁻¹) ∧ ∀ x y : G, x*y = y*x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (G : Type*) [Group G] [Fintype G] (φ : G ≃* G) (hφ : ∃ S : Finset G, S.card > 3 * Fintype.card G / 4 ∧ ∀ x ∈ S, φ x = x⁻¹) : (∀ y : G, φ y = y⁻¹) ∧ ∀ x y : G, x * y = y * x := by
  obtain ⟨S, hS, hφS⟩ := hφ
  apply exercise_2_5_52_assumed φ hφS
  rw [Fintype.card_coe]
  have hFourNat : 0 < (4 : ℕ) := Nat.succ_pos 3
  have hNat : 3 * Fintype.card G < S.card * 4 :=
    (Nat.div_lt_iff_lt_mul hFourNat).mp hS
  have hRat : (3 : ℚ) * Fintype.card G < S.card * 4 := by
    exact_mod_cast hNat
  have hDecimal : (0.75 : ℚ) = 3 / 4 := by
    rw [Rat.ofScientific_def_eq_if, if_pos rfl]
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    exact_mod_cast (show 75 * 4 = 3 * 10 ^ 2 by rfl)
  rw [hDecimal, div_mul_eq_mul_div]
  have hFourRat : (0 : ℚ) < 4 := by
    exact_mod_cast hFourNat
  rw [div_le_iff₀ hFourRat]
  exact hRat.le
