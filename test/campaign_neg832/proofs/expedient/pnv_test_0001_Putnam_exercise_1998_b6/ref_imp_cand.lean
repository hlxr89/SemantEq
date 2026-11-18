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
  obtain ⟨n, hn, h⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.toNat, by omega, ?_⟩
  intro he
  apply h
  refine ⟨n, ?_⟩
  have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
  have hnR : (n.toNat : ℝ) = n := by exact_mod_cast hn'
  simpa [hnR] using he
