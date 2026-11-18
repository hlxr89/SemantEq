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
  obtain ⟨n, hn, hnsqrt⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.toNat, ?_, ?_⟩
  · omega
  intro hzero
  apply hnsqrt
  refine ⟨0, ?_⟩
  have hn_cast : (n.toNat : ℤ) = n := by omega
  have hn_cast_real : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hn_cast
  have hpoly : (n : ℝ) ^ 3 + (a : ℝ) * n ^ 2 + (b : ℝ) * n + (c : ℝ) = 0 := by
    simpa [hn_cast_real] using hzero
  rw [hpoly]
  norm_num
