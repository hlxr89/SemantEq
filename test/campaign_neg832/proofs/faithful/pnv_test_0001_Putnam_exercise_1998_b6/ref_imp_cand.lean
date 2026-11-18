import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b c : ℤ) : ∃ (n : ℕ) (H : 0 < n), √(n^3 + a*n^2 + b*n + c) ≠ n := by
  obtain ⟨n, hn, hnonsquare⟩ := exercise_1998_b6_assumed a b c
  have hn0 : 0 ≤ n := le_of_lt hn
  have hcastInt : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  have hposInt : (0 : ℤ) < (n.toNat : ℤ) := by simpa only [hcastInt] using hn
  have hpos : 0 < n.toNat := by exact_mod_cast hposInt
  have hcastReal : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hcastInt
  refine ⟨n.toNat, hpos, ?_⟩
  intro heq
  apply hnonsquare
  refine ⟨n, ?_⟩
  simpa only [hcastReal] using heq
