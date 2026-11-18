import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [CommRing R] [DecidableEq R] (hR : ∀ n : ℕ, ∃ x : R, x ≠ 0 ∧ ∀ m : ℕ, m < n → x ^ (n + 1) ≠ 0) : ∃ (I : Ideal R) (H : I.IsPrime), ∀ J : Ideal R, J.IsPrime → I ≤ J → J = I := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_1_10 {f : ℕ → MvPolynomial ℕ ℤ}
  (hf : f = λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)):
  Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) := by
  subst f
  let I : Ideal (MvPolynomial ℕ ℤ) :=
    span (range fun i : ℕ ↦ MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1))
  let a (n i : ℕ) : ℤ :=
    if i = 2*n then 1 else if i = 2*n+1 then 0 else if Even i then 0 else 1
  let P (n : ℕ) : Ideal (MvPolynomial ℕ ℤ) := RingHom.ker (MvPolynomial.eval (a n))
  have hP (n : ℕ) : (P n).IsPrime := RingHom.ker_isPrime _
  have hIP (n : ℕ) : I ≤ P n := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    change MvPolynomial.eval (a n)
      (MvPolynomial.X (2 * k) * MvPolynomial.X (2 * k + 1)) = 0
    simp only [map_mul, MvPolynomial.eval_X]
    by_cases hkn : k = n
    · subst k
      simp [a]
    · have h₁ : 2 * k ≠ 2 * n := by omega
      have h₂ : 2 * k ≠ 2 * n + 1 := by omega
      simp [a, h₁, h₂]
  let q (n : ℕ) : Ideal (MvPolynomial ℕ ℤ) :=
    Classical.choose (Ideal.exists_minimalPrimes_le (hIP n))
  have hqmem (n : ℕ) : q n ∈ I.minimalPrimes :=
    (Classical.choose_spec (Ideal.exists_minimalPrimes_le (hIP n))).1
  have hqle (n : ℕ) : q n ≤ P n :=
    (Classical.choose_spec (Ideal.exists_minimalPrimes_le (hIP n))).2
  have hprod (n k : ℕ) :
      MvPolynomial.X (2*k) * MvPolynomial.X (2*k+1) ∈ q n := by
    apply (hqmem n).1.2
    exact Ideal.subset_span ⟨k, rfl⟩
  have heven_not (n : ℕ) : MvPolynomial.X (2*n) ∉ q n := by
    intro h
    have hp := hqle n h
    change MvPolynomial.eval (a n) (MvPolynomial.X (2*n)) = 0 at hp
    simpa [a] using hp
  have heven_mem {n k : ℕ} (hnk : n ≠ k) : MvPolynomial.X (2*n) ∈ q k := by
    rcases (Ideal.IsPrime.mem_or_mem (Ideal.minimalPrimes_isPrime (hqmem k)) (hprod k n)) with h | h
    · exact h
    · exfalso
      have hp := hqle k h
      change MvPolynomial.eval (a k) (MvPolynomial.X (2*n+1)) = 0 at hp
      have h₁ : 2 * n + 1 ≠ 2 * k := by omega
      have h₂ : 2 * n + 1 ≠ 2 * k + 1 := by omega
      simp [a, h₁, h₂] at hp
      exact hnk hp
  have hqinj : Function.Injective q := by
    intro n k h
    by_contra hnk
    exact heven_not n (h ▸ heven_mem hnk)
  have hIinf : I.minimalPrimes.Infinite := by
    rw [← Set.infinite_coe_iff]
    exact Infinite.of_injective (fun n : ℕ ↦ (⟨q n, hqmem n⟩ : I.minimalPrimes)) fun _ _ h ↦
      hqinj (Subtype.ext_iff.mp h)
  rw [Ideal.minimalPrimes_eq_comap] at hIinf
  rw [Set.infinite_coe_iff]
  intro hfin
  exact hIinf (hfin.image fun J ↦ Ideal.comap (Ideal.Quotient.mk I) J)
