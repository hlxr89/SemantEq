import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_9_1_10_assumed {f : ℕ → MvPolynomial ℕ ℤ}
  (hf : f = λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)):
  Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : ∃ (P : ℕ → Ideal (Polynomial (ℤ))), (∀ n, Ideal.IsPrime (P n)) ∧ (∀ n m, n ≠ m → P n ≠ P m) := by
  refine ⟨fun n => RingHom.ker (Polynomial.evalRingHom (n : ℤ)), fun n => RingHom.ker_isPrime _, ?_⟩
  intro n m hnm
  change RingHom.ker (Polynomial.evalRingHom (n : ℤ)) ≠
    RingHom.ker (Polynomial.evalRingHom (m : ℤ))
  intro h
  have hx : Polynomial.X - Polynomial.C (n : ℤ) ∈
      RingHom.ker (Polynomial.evalRingHom (n : ℤ)) := by
    rw [Polynomial.ker_evalRingHom]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [h] at hx
  simp [RingHom.mem_ker] at hx
  omega
