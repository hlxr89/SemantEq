import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a b c : ℤ} : ∃ (n : ℕ) (H : 0 < n), ¬(n : ℝ) ^ 3 + a * n ^ 2 + b * n + c = 0 := by
  obtain ⟨n, hn, hnonint⟩ := exercise_1998_b6_assumed a b c
  have hn_cast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
  have hn_pos : 0 < n.toNat := Int.natCast_pos.mp (by
    rw [hn_cast]
    exact hn)
  refine ⟨n.toNat, hn_pos, ?_⟩
  intro hzero
  apply hnonint
  refine ⟨0, ?_⟩
  rw [← hn_cast]
  simp only [Int.cast_natCast]
  rw [hzero, Real.sqrt_zero]
  exact Int.cast_zero.symm

