import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_1_8_assumed {p m n: ℕ} {F : Type*} [Field F]
  (hp : p ≠ 0) (hn : n > 0)
  (hF : CharP F p) (a b : F) (hm : m = p ^ n) :
  (a + b) ^ m = a^m + b^m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {F : Type*} [Field F] {p : ℕ} {n : ℕ} [hp : Fact (Nat.Prime p)] [CharP F p] (a b : F) : (a + b)^(p ^ n) = a^(p^n) + b^(p^n) := by
  have hFrob (x y : F) : (x + y) ^ p = x ^ p + y ^ p :=
    exercise_5_1_8_assumed (p := p) (m := p) (n := 1)
      hp.out.ne_zero (by omega) (inferInstance : CharP F p) x y (by simp)
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (a + b) ^ (p ^ (n + 1)) = ((a + b) ^ (p ^ n)) ^ p := by
          rw [pow_succ, pow_mul]
        _ = (a ^ (p ^ n) + b ^ (p ^ n)) ^ p := by rw [ih]
        _ = (a ^ (p ^ n)) ^ p + (b ^ (p ^ n)) ^ p := hFrob _ _
        _ = a ^ (p ^ (n + 1)) + b ^ (p ^ (n + 1)) := by
          rw [pow_succ, pow_mul, pow_mul]
