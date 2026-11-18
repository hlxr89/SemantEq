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
  refine ⟨fun n => RingHom.ker (Polynomial.evalRingHom (n : ℤ)), ?_, ?_⟩
  · intro n
    exact RingHom.ker_isPrime _
  · intro n m hnm hEq
    change RingHom.ker (Polynomial.evalRingHom (n : ℤ)) =
      RingHom.ker (Polynomial.evalRingHom (m : ℤ)) at hEq
    have hn : Polynomial.X - Polynomial.C (n : ℤ) ∈
        RingHom.ker (Polynomial.evalRingHom (n : ℤ)) := by
      simp [RingHom.mem_ker]
    rw [hEq] at hn
    have hcast : (m : ℤ) = (n : ℤ) := by
      simp [RingHom.mem_ker] at hn
      omega
    apply hnm
    exact_mod_cast hcast.symm
