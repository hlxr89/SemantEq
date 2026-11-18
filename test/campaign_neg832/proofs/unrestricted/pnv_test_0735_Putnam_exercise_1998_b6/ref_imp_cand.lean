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
  obtain ⟨n, hn, hnot⟩ := exercise_1998_b6_assumed a b c
  have hn0 : 0 ≤ n := le_of_lt hn
  let k : ℕ := n.toNat
  have hk : (k : ℤ) = n := by
    simpa [k] using Int.toNat_of_nonneg hn0
  refine ⟨k, ?_⟩
  rintro ⟨m, hm⟩
  apply hnot
  refine ⟨(m : ℤ), ?_⟩
  have hpZ : n^3 + a*n^2 + b*n + c = (m : ℤ)^2 := by
    rw [← hk]
    exact hm.symm
  have hp : (n : ℝ)^3 + (a : ℝ)*(n : ℝ)^2 + (b : ℝ)*(n : ℝ) + c =
      (m : ℝ)^2 := by
    exact_mod_cast hpZ
  rw [hp]
  simp
