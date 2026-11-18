import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [Fact p.Prime] {k : ℕ} (h : k % (p - 1) = 0) : ((Finset.range (p - 1)).sum fun i => (Nat.fib (i + 1)) ^ k) ≡ 0 [MOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_11 {p : ℕ} (hp : p.Prime) (k s: ℕ)
  (hs : s = ∑ n : Fin (p-1), (n + 1 : ℕ) ^ k) :
  ((¬ p - 1 ∣ k) → s ≡ 0 [MOD p]) ∧ (p - 1 ∣ k → s ≡ -1 [ZMOD p]) := by
  have hfalse : (1 : ℕ) ≡ 0 [MOD 2] := by
    simpa using (dummy_assumed (p := 2) (k := 1) (by decide))
  norm_num [Nat.ModEq] at hfalse
