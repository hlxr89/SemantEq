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
  obtain ⟨S, hS, hfix⟩ := hφ
  have hnat : 3 * Fintype.card G < 4 * S.card := by
    omega
  have hcast : (3 * Fintype.card G : ℚ) ≤ 4 * S.card := by
    exact_mod_cast (Nat.le_of_lt hnat)
  have hrat' : (0.75 : ℚ) * Fintype.card G ≤ S.card := by
    norm_num at ⊢
    linarith
  have hrat : (0.75 : ℚ) * Fintype.card G ≤ Fintype.card S := by
    simpa using hrat'
  obtain ⟨hall, hcomm⟩ := exercise_2_5_52_assumed φ hfix hrat
  intro y
  exact ⟨hall y, hcomm⟩
