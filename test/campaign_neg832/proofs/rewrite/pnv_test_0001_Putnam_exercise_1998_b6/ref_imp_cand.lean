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
  obtain ⟨n, hn, hroot⟩ := exercise_1998_b6_assumed a b c
  have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
  have hnpos : 0 < n.toNat := Int.natCast_pos.mp (hncast.symm ▸ hn)
  refine ⟨n.toNat, hnpos, ?_⟩
  intro heq
  apply hroot
  refine ⟨n, ?_⟩
  rw [← hncast]
  exact heq
