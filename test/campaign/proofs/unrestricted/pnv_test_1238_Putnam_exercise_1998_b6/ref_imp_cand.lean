import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a b c : ℤ} : ∃ (n : ℕ) (hn : 0 < n), ¬ ∃ (m : ℤ), n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2 := by
  rcases exercise_1998_b6_assumed a b c with ⟨n, hn, hbad⟩
  have hn0 : 0 ≤ n := le_of_lt hn
  have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  have hntpos : 0 < n.toNat := by
    have : (0 : ℤ) < (n.toNat : ℤ) := by simpa [hncast] using hn
    exact_mod_cast this
  refine ⟨n.toNat, hntpos, ?_⟩
  rintro ⟨m, hm⟩
  apply hbad
  refine ⟨|m|, ?_⟩
  rw [← hncast]
  have hm' : ((n.toNat : ℤ) : ℝ) ^ 3 + (a : ℝ) * ((n.toNat : ℤ) : ℝ) ^ 2 +
      (b : ℝ) * ((n.toNat : ℤ) : ℝ) + c = (m : ℝ) ^ 2 := by
    exact_mod_cast hm
  rw [hm', Real.sqrt_sq_eq_abs]
  norm_cast
