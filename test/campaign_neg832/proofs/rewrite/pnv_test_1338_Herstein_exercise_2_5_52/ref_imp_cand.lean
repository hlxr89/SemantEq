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
theorem dummy {G : Type*} [Finite G] [Group G] (φ : G ≃* G) (hφ : ∀ x, x ^ 4 = x → φ x = x⁻¹) : ∀ y, φ y = y⁻¹ := by
  -- not proved: the candidate is false (for example on a group of order 5), so only forbidden explosion from the inconsistent assumed theorem could prove it
  sorry
