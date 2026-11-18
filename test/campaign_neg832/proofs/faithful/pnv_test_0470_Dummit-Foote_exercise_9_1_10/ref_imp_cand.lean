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
  classical
  let f : ℕ → MvPolynomial ℕ ℤ :=
    λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)
  let T := minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))
  haveI : Infinite T := exercise_9_1_10_assumed (f := f) rfl
  let e : ℕ ↪ T := Infinite.natEmbedding T
  let index (n : ℕ) : ℕ := Nat.find (show ∃ k, e k = e n from ⟨n, rfl⟩)
  have hindex (n : ℕ) : index n = n := by
    apply e.injective
    exact Nat.find_spec (show ∃ k, e k = e n from ⟨n, rfl⟩)
  let P (n : ℕ) : Ideal (Polynomial ℤ) :=
    RingHom.ker (Polynomial.evalRingHom (Int.ofNat (index n)))
  refine ⟨P, ?_, ?_⟩
  · intro n
    exact RingHom.ker_isPrime (Polynomial.evalRingHom (Int.ofNat (index n)))
  · intro n m hnm hP
    have hx : Polynomial.X - Polynomial.C (Int.ofNat (index n)) ∈ P n := by
      simp [P, RingHom.mem_ker]
    have hx' : Polynomial.X - Polynomial.C (Int.ofNat (index n)) ∈ P m := by
      rw [← hP]
      exact hx
    have heq : index m = index n := by
      have : Int.ofNat (index m) - Int.ofNat (index n) = 0 := by
        simpa [P, RingHom.mem_ker] using hx'
      exact Int.ofNat_inj.mp (sub_eq_zero.mp this)
    apply hnm
    rw [← hindex n, ← hindex m, heq]
