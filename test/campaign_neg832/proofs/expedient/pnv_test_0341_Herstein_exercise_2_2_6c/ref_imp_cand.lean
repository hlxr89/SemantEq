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
theorem dummy {G : Type*} [Group G] (n : ℕ) (hn : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) (a b : G) : (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  by_cases hle : n ≤ 1
  · interval_cases n <;> simp
  · exact exercise_2_2_6c_assumed (Nat.lt_of_not_ge hle) hn a b
