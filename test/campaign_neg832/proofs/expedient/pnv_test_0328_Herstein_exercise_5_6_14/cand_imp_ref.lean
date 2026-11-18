import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] [CharP F p] (m : ℕ) (hn : m = p ^ n) : ∀ (x : F), x ^ m ≠ x → x ≠ (x ^ p) ^ n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  rw [Polynomial.separable_def]
  have hm0 : (m : F) = 0 := by
    rw [hm, Nat.cast_pow, CharP.cast_eq_zero F p]
    exact zero_pow hn.ne'
  convert isCoprime_one_right.neg_right using 1 <;>
    simp [Polynomial.derivative_sub, Polynomial.derivative_X_pow, hm0]
