import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] {p : ℕ} [CharP F p] (n : ℕ) [Fact (p = 0 ∨ p = 1 ∨ p ≠ 1)] (hp : p = 0 ∨ p = 1 ∨ p ≠ 1) : IsCyclic (Multiplicative (ZMod (p ^ n))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  subst m
  rw [Polynomial.separable_def]
  convert isCoprime_one_right.neg_right (R := F[X]) using 1
  rw [derivative_sub, derivative_X, derivative_X_pow, Nat.cast_pow,
    CharP.cast_eq_zero F p, zero_pow (Nat.ne_of_gt hn), C_0, zero_mul, zero_sub]
