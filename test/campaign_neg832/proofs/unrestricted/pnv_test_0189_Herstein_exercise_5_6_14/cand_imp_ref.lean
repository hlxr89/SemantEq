import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p] (n : ℕ) : ∀ x y : F, (x ^ (p ^ n) = x) → (y ^ (p ^ n) = y) → x = y → x = y := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  rw [Polynomial.separable_def]
  simp [Polynomial.derivative_sub, Polynomial.derivative_X_pow, hm, hn.ne']
  exact isCoprime_one_right.neg_right
