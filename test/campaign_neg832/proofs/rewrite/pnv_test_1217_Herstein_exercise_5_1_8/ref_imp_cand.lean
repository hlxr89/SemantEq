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
  have hstep := exercise_5_1_8_assumed hp.out.ne_zero (n := 1) Nat.zero_lt_one
    (inferInstance : CharP F p) (a ^ (p ^ n)) (b ^ (p ^ n)) rfl
  simp only [pow_one] at hstep
  have hlarge := exercise_5_1_8_assumed hp.out.ne_zero (n := n + 1) (Nat.zero_lt_succ n)
    (inferInstance : CharP F p) a b rfl
  rw [pow_succ] at hlarge
  apply (frobenius F p).injective
  change ((a + b) ^ (p ^ n)) ^ p = (a ^ (p ^ n) + b ^ (p ^ n)) ^ p
  rw [hstep]
  simp only [← pow_mul]
  exact hlarge
