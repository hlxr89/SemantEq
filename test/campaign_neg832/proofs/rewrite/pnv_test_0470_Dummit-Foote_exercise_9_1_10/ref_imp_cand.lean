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
  let f : ℕ → MvPolynomial ℕ ℤ :=
    λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)
  have hInfinite := exercise_9_1_10_assumed (f := f) rfl
  let e := @Infinite.natEmbedding (minimalPrimes
    (MvPolynomial ℕ ℤ ⧸ span (range f))) hInfinite
  refine ⟨fun n => RingHom.ker (Polynomial.evalRingHom (n : ℤ)), ?_, ?_⟩
  · intro n
    exact RingHom.ker_isPrime _
  · intro n m hnm hEq
    have hem : e n ≠ e m := fun h => hnm (e.injective h)
    have hx : Polynomial.X - Polynomial.C (n : ℤ) ∈
        RingHom.ker (Polynomial.evalRingHom (n : ℤ)) := by
      rw [RingHom.mem_ker]
      rw [map_sub]
      rw [Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_self _
    change RingHom.ker (Polynomial.evalRingHom (n : ℤ)) =
      RingHom.ker (Polynomial.evalRingHom (m : ℤ)) at hEq
    rw [hEq] at hx
    have hcast : (n : ℤ) = (m : ℤ) := by
      rw [RingHom.mem_ker] at hx
      rw [map_sub] at hx
      rw [Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_C] at hx
      exact (sub_eq_zero.mp hx).symm
    exact hem (congrArg e (Int.ofNat_inj.mp hcast))
