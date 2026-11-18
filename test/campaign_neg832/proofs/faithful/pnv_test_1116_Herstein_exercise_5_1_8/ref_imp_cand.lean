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
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hhigh := exercise_5_1_8_assumed (p := p) (m := p ^ (n + 1))
    (n := n + 1) (F := F) hp0 (Nat.zero_lt_succ n) (by infer_instance) a b rfl
  have hbase := exercise_5_1_8_assumed (p := p) (m := p) (n := 1) (F := F)
    hp0 (by simp) (by infer_instance) (a ^ (p ^ n)) (b ^ (p ^ n)) (by simp)
  apply (frobenius_inj F p).eq_iff.mp
  change ((a + b) ^ (p ^ n)) ^ p = (a ^ (p ^ n) + b ^ (p ^ n)) ^ p
  calc
    ((a + b) ^ (p ^ n)) ^ p = (a + b) ^ (p ^ (n + 1)) := by
      rw [pow_succ, pow_mul]
    _ = a ^ (p ^ (n + 1)) + b ^ (p ^ (n + 1)) := hhigh
    _ = (a ^ (p ^ n)) ^ p + (b ^ (p ^ n)) ^ p := by
      rw [pow_succ, pow_mul, pow_mul]
    _ = (a ^ (p ^ n) + b ^ (p ^ n)) ^ p := hbase.symm
