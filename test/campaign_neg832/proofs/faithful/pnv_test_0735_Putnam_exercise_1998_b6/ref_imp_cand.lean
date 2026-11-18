import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a b c : ℤ} : ∃ n : ℕ, ¬∃ m : ℕ, m^2 = n^3 + a * n^2 + b * n + c := by
  obtain ⟨n, hn, hnsqrt⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.toNat, ?_⟩
  rintro ⟨m, hm⟩
  apply hnsqrt
  refine ⟨(m : ℤ), ?_⟩
  have hn_cast : (n.toNat : ℤ) = n := by omega
  rw [hn_cast] at hm
  have hpoly : n ^ 3 + a * n ^ 2 + b * n + c = (m : ℤ) ^ 2 := hm.symm
  have hpoly_real : (n : ℝ) ^ 3 + (a : ℝ) * n ^ 2 + (b : ℝ) * n + c = (m : ℝ) ^ 2 := by
    exact_mod_cast hpoly
  rw [hpoly_real]
  simp
