import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_2_6c_assumed {G : Type*} [Group G] {n : ℕ} (hn : n > 1)
  (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
  ∀ (a b : G), (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type u} [Group G] (h : ∀ a b : G, ((a*b)^n = a^n * b^n)) (a b : G) : (a * b * a⁻¹ * b⁻¹)^(n*(n-1)) = 1 := by
  by_cases hn : n > 1 -- non-rewrite step
  · exact exercise_2_2_6c_assumed hn h a b
  · have hnle : n ≤ 1 := Nat.le_of_not_gt hn
    rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hnle) with rfl | rfl
    · exact pow_zero _
    · exact pow_zero _
