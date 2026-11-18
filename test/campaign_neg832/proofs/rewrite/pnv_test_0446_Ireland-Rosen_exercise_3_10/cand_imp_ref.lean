import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} (h : n ≠ 2 ∧ n ≠ 3) : n - 1 ≡ 0 [MOD n] ∨ n = 4:= by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_10 {n : ℕ+} (hn0 : ¬ n.Prime) :
  Nat.factorial (n-1) ≡ 0 [MOD n] ↔ n ≠ 4 := by
  -- not proved: only an explicitly forbidden ex-falso argument can transport the inconsistent candidate statement
  sorry
