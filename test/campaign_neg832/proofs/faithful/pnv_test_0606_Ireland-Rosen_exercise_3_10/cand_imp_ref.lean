import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) (hn : ¬n.Prime) : n - 1 ≡ 0 [MOD n] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_10 {n : ℕ+} (hn0 : ¬ n.Prime) :
  Nat.factorial (n-1) ≡ 0 [MOD n] ↔ n ≠ 4 := by
  have hmod := dummy_assumed (n : ℕ) hn0
  have hnpos : 0 < (n : ℕ) := n.prop
  have hnle : (n : ℕ) - 1 < (n : ℕ) := by omega
  change ((n : ℕ) - 1) % (n : ℕ) = 0 % (n : ℕ) at hmod
  have hz : (n : ℕ) - 1 = 0 := by
    simpa [Nat.mod_eq_of_lt hnle] using hmod
  have hn_one : (n : ℕ) = 1 := by omega
  have hn_eq : n = 1 := by
    apply Subtype.ext
    exact hn_one
  subst n
  norm_num [Nat.ModEq]
