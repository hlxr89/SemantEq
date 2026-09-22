import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) (hnp : ¬Nat.Prime n) : n.pred.factorial % n = 0 ∨ n = 4 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_10 {n : ℕ+} (hn0 : ¬ n.Prime) :
  Nat.factorial (n-1) ≡ 0 [MOD n] ↔ n ≠ 4 := by
  have h := dummy_assumed (n : ℕ) hn0
  constructor
  · intro hmod
    rcases h with hzero | hfour
    · intro hn4
      rw [hn4] at hzero
      exact Nat.noConfusion hzero
    · intro _
      have hn4 : n = 4 := Subtype.ext hfour
      rw [hn4] at hmod
      exact Nat.noConfusion hmod
  · intro hn4
    rcases h with hzero | hfour
    · exact hzero
    · exact (hn4 (Subtype.ext hfour)).elim
