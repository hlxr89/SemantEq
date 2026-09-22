import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a b c : ℤ} : ∃ n : ℕ, ¬ ∃ m : ℤ, m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
  obtain ⟨n, hn, h⟩ := exercise_1998_b6_assumed a b c
  have hnn : 0 ≤ n := le_of_lt hn
  refine ⟨n.toNat, ?_⟩
  rintro ⟨m, hm⟩
  apply h
  refine ⟨|m|, ?_⟩
  have hm' : m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
    simpa [Int.toNat_of_nonneg hnn] using hm
  calc
    Real.sqrt (n^3 + a*n^2 + b*n + c) = Real.sqrt ((m : ℝ) ^ 2) := by
      congr 1
      exact_mod_cast hm'.symm
    _ = |(m : ℝ)| := Real.sqrt_sq_eq_abs _
    _ = (|m| : ℤ) := by norm_num
