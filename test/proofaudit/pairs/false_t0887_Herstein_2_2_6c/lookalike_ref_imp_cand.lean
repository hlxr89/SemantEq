import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary (Group, pow, inv); neither side
-- has local defs, so the unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_2_2_6c_assumed {G : Type*} [Group G] {n : ℕ} (hn : n > 1)
    (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
    ∀ (a b : G), (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem commutator_pow_eq_one_cand {G : Type*} [Group G] {n : ℕ}
    (h : ∀ (a b : G), (a * b)^n = a^n * b^n) (a b : G) :
    (a * b * a⁻¹ * b⁻¹)^(n*(n-1)) = 1 := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · exact exercise_2_2_6c_assumed hn h a b
  · -- the exponent normalises away on the low range
    have hn' : n ≤ 1 := hn
    interval_cases n
    · rw [Nat.zero_mul, pow_zero]
    · rw [Nat.sub_self, Nat.mul_zero, pow_zero]
