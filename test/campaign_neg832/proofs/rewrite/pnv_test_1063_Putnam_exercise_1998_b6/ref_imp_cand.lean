import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b c : ℤ) (h : ∃ n : ℕ, √(n^3+a*n^2+b*n+c) ≠ n) : ∃ n : ℕ, 0 < n ∧ √(n^3+a*n^2+b*n+c) ≠ n := by
  obtain ⟨n, hnpos, hn⟩ := exercise_1998_b6_assumed a b c
  have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hnpos)
  have hnatpos : 0 < n.toNat := by
    apply Int.natCast_pos.mp
    rw [hcast]
    exact hnpos
  refine ⟨n.toNat, hnatpos, ?_⟩
  intro heq
  apply hn
  refine ⟨n, ?_⟩
  have hcastReal : (n.toNat : ℝ) = (n : ℝ) := by
    rw [← Int.cast_natCast, hcast]
  simpa only [hcastReal] using heq
