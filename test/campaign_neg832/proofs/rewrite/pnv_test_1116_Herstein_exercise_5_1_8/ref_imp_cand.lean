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
theorem dummy (F : Type*) [Field F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] (m n : ℕ) (a b : F) : (a + b) ^ (p ^ n) = a ^ (p ^ n) + b ^ (p ^ n) := by
  have h := exercise_5_1_8_assumed (p := p) (m := p ^ (n + 1)) (n := n + 1)
    hp.out.ne_zero (Nat.zero_lt_succ n) (inferInstance : CharP F p) a b rfl
  apply frobenius_inj F p
  rw [frobenius_def, frobenius_def, ← add_pow_char]
  simpa only [← pow_mul, pow_succ] using h
