import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} (hn : ¬Prime n) : n.pred.factorial = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_10 {n : ℕ+} (hn0 : ¬ n.Prime) :
  Nat.factorial (n-1) ≡ 0 [MOD n] ↔ n ≠ 4 := by
  have h : (1 : ℕ) = 0 := by
    simpa using (dummy_assumed (n := 0) (by norm_num))
  omega
