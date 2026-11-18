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
theorem dummy {G : Type*} [Group G] (n : ℕ) (h : ∀ a b : G, (a * b) ^ n = a ^ n * b ^ n) (a b : G) : (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  cases n with
  | zero =>
      simp only [Nat.zero_mul, pow_zero]
  | succ n =>
      cases n with
      | zero =>
          simp only [Nat.zero_add, Nat.one_sub, if_neg Nat.one_ne_zero, Nat.mul_zero, pow_zero]
      | succ n =>
          exact exercise_2_2_6c_assumed (Nat.succ_lt_succ (Nat.zero_lt_succ n)) h a b
