import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (n : ℕ) [h0 : NeZero n] (a : G) (b : G) (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) : Commute a b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_6c {G : Type*} [Group G] {n : ℕ} (hn : n > 1)
  (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
  ∀ (a b : G), (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  letI : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_one.trans hn)⟩
  intro a b
  have hab : Commute a b := dummy_assumed n a b h
  rw [hab.eq, mul_assoc b a a⁻¹, mul_inv_cancel, mul_one, mul_inv_cancel, one_pow]
