import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] : ∃ (f : R[X]) (hf : ∀ i : ℕ, f.degree ≠ 2*i), ∃ (P : Ideal (R[X])), Ideal.IsPrime P ∧ Ideal.IsMaximal P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_1_10 {f : ℕ → MvPolynomial ℕ ℤ}
  (hf : f = λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)):
  Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) := by
  obtain ⟨g, hg, P, hP, _⟩ := dummy_assumed (R := ZMod 1)
  exact (hP.ne_top (Subsingleton.elim P ⊤)).elim
