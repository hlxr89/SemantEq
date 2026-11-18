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
theorem dummy {F : Type*} [Field F] [CharP F p] (p_neq_zero : p ≠ 0) {m : ℕ} (h_m : m = p^n) (a b : F) : (a + b) ^ m = a ^ m + b ^ m := by
  cases n with
  | zero =>
      have h := exercise_5_1_8_assumed (p := p) (m := p) (n := 1)
        p_neq_zero (by omega) (inferInstance : CharP F p) a b (by simp)
      simpa [h_m] using congrArg (fun _ : F => a + b) h
  | succ n =>
      exact exercise_5_1_8_assumed p_neq_zero (by omega)
        (inferInstance : CharP F p) a b h_m
