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
  obtain ⟨n, hn, hns⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.toNat, ?_⟩
  rintro ⟨m, hm⟩
  apply hns
  refine ⟨m, ?_⟩
  have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
  have hmZ : (m : ℤ)^2 = n^3 + a*n^2 + b*n + c := by
    rw [← hn']
    exact_mod_cast hm
  have hmR : (n : ℝ)^3 + a*n^2 + b*n + c = (m : ℝ)^2 := by
    exact_mod_cast hmZ.symm
  rw [hmR, Real.sqrt_sq_eq_abs]
  simp
