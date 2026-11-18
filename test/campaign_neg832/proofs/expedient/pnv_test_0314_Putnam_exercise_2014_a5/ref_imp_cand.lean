import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2014_a5_assumed (P : ℕ → Polynomial ℤ)
  (hP : ∀ n, P n = ∑ i : Fin n, (n+1) * Polynomial.X ^ n) :
  ∀ (j k : ℕ), j ≠ k → IsCoprime (P j) (P k) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (S : Set ℕ) (hS : S.Finite) (x : ℕ) (hx : ∀ n : ℕ, n ∈ S → x ∣ n) : ∃ y : ℕ, ∀ n : ℕ, n ∈ S → y ∣ n ∧ y ∣ n - x := by
  refine ⟨1, ?_⟩
  intro n hn
  exact ⟨one_dvd n, one_dvd (n - x)⟩
