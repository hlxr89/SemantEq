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
  obtain ⟨z, hz, hnonsquare⟩ := exercise_1998_b6_assumed a b c
  have hz0 : 0 ≤ z := le_of_lt hz
  let n : ℕ := z.toNat
  have hn : (n : ℤ) = z := by
    simp [n, Int.toNat_of_nonneg hz0]
  have hnR : (n : ℝ) = (z : ℝ) := by
    exact_mod_cast hn
  refine ⟨n, ?_, ?_⟩
  · have : (0 : ℤ) < (n : ℤ) := by simpa [hn] using hz
    exact_mod_cast this
  · intro heq
    apply hnonsquare
    refine ⟨z, ?_⟩
    rw [hnR] at heq
    exact heq
