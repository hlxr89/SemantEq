import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p] (n : ℕ) : (∃ (x : F), x ^ (p ^ n) = x) → (∀ x y : F, x ≠ y → x ^ (p ^ n) ≠ y ^ (p ^ n)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  letI : Fact (Nat.Prime p) := ⟨CharP.char_prime_of_ne_zero (R := F) hp⟩
  have hpow_ne : p ^ n ≠ 0 := by
    intro hpow_zero
    have hne := dummy_assumed (F := F) p n
      ⟨0, by simp only [zero_pow (pow_ne_zero n hp)]⟩
      (0 : F) 1 zero_ne_one
    apply hne
    rw [hpow_zero, pow_zero, pow_zero]
  rw [hm, separable_def]
  have hcast : ((p ^ n : ℕ) : F) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero F p, zero_pow hn.ne']
  rw [derivative_sub, derivative_pow, derivative_X, hcast, C_0]
  simp only [zero_mul, zero_sub]
  exact IsCoprime.neg_right isCoprime_one_right
