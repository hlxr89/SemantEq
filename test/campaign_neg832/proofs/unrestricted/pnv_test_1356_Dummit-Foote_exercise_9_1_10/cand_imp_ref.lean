import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] (I : Ideal R) [IsPrime I] (h : ∀ n : ℕ, ∃ I : Ideal R, IsPrime I ∧ I ≤ I ^ 2 ^ n) : ∃ n : ℕ, ∃ I : Ideal (R × R), IsPrime I ∧ I ≤ I ^ 2 ^ n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_1_10 {f : ℕ → MvPolynomial ℕ ℤ}
  (hf : f = λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)):
  Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) := by
  classical
  let A : Ideal (MvPolynomial ℕ ℤ) := span (range f)
  let s : ℕ → Set ℕ := fun n => {i | i = 2*n ∨ ∃ k, k ≠ n ∧ i = 2*k+1}
  let t (n : ℕ) := {i : ℕ // i ∉ s n}
  let e (n : ℕ) : s n ⊕ t n ≃ ℕ := Equiv.sumCompl (fun i => i ∈ s n)
  let E (n : ℕ) : MvPolynomial ℕ ℤ ≃+* MvPolynomial (s n) (MvPolynomial (t n) ℤ) :=
    (MvPolynomial.renameEquiv ℤ (e n).symm).toRingEquiv.trans
      (MvPolynomial.sumRingEquiv ℤ (s n) (t n))
  let K (n : ℕ) : Ideal (MvPolynomial (s n) (MvPolynomial (t n) ℤ)) :=
    MvPolynomial.idealOfVars (s n) (MvPolynomial (t n) ℤ)
  let P (n : ℕ) : Ideal (MvPolynomial ℕ ℤ) := (K n).comap (E n)

  have hEsel (n i : ℕ) (hi : i ∈ s n) :
      E n (MvPolynomial.X i) = MvPolynomial.X (⟨i, hi⟩ : s n) := by
    simp [E, e, Equiv.sumCompl, hi, MvPolynomial.sumRingEquiv]
  have hEnsel (n i : ℕ) (hi : i ∉ s n) :
      E n (MvPolynomial.X i) =
        MvPolynomial.C (MvPolynomial.X (⟨i, hi⟩ : t n)) := by
    simp [E, e, Equiv.sumCompl, hi, t, MvPolynomial.sumRingEquiv]
  have hKker (n : ℕ) : K n = RingHom.ker MvPolynomial.constantCoeff := by
    ext p
    rw [show K n = Ideal.span (MvPolynomial.X '' (Set.univ : Set (s n))) by
      simp [K, MvPolynomial.idealOfVars]]
    rw [MvPolynomial.mem_ideal_span_X_image]
    simp only [Set.mem_univ, true_and, RingHom.mem_ker]
    change (∀ m ∈ p.support, ∃ i, (m : s n →₀ ℕ) i ≠ 0) ↔ p.coeff 0 = 0
    constructor
    · intro hp
      by_contra hz
      obtain ⟨i, hi⟩ := hp 0 (Finsupp.mem_support_iff.mpr hz)
      exact hi rfl
    · intro hp m hm
      have hm0 : m ≠ 0 := by
        intro hzero
        subst m
        exact Finsupp.mem_support_iff.mp hm hp
      simpa [Finsupp.ext_iff] using hm0
  have hKprime (n : ℕ) : (K n).IsPrime := by
    rw [hKker]
    exact RingHom.ker_isPrime MvPolynomial.constantCoeff
  have hPprime (n : ℕ) : (P n).IsPrime := by
    exact Ideal.IsPrime.comap (E n)
  have hPsel (n i : ℕ) (hi : i ∈ s n) : MvPolynomial.X i ∈ P n := by
    change E n (MvPolynomial.X i) ∈ K n
    rw [hEsel n i hi]
    exact Ideal.subset_span (Set.mem_range_self _)
  have hPnsel (n i : ℕ) (hi : i ∉ s n) : MvPolynomial.X i ∉ P n := by
    change E n (MvPolynomial.X i) ∉ K n
    rw [hEnsel n i hi, hKker]
    intro hx
    rw [RingHom.mem_ker, MvPolynomial.constantCoeff_C (s n)] at hx
    exact MvPolynomial.X_ne_zero (R := ℤ) (⟨i, hi⟩ : t n) hx
  have hseven (n k : ℕ) : 2*k ∈ s n ↔ k = n := by
    simp [s]
    omega
  have hsodd (n k : ℕ) : 2*k+1 ∈ s n ↔ k ≠ n := by
    simp [s]
    omega
  have hAP (n : ℕ) : A ≤ P n := by
    change span (range f) ≤ P n
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    rw [hf]
    by_cases hk : k = n
    · exact (P n).mul_mem_right _ (hPsel n (2*k) ((hseven n k).2 hk))
    · exact (P n).mul_mem_left _ (hPsel n (2*k+1) ((hsodd n k).2 hk))
  have hPeq (n : ℕ) : P n = Ideal.span (MvPolynomial.X '' s n) := by
    change (K n).comap (E n) = Ideal.span (MvPolynomial.X '' s n)
    rw [← Ideal.map_symm]
    change (MvPolynomial.idealOfVars (s n) (MvPolynomial (t n) ℤ)).map (E n).symm =
      Ideal.span (MvPolynomial.X '' s n)
    rw [MvPolynomial.idealOfVars, Ideal.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      refine ⟨j.val, j.property, ?_⟩
      apply (E n).injective
      simp only [RingEquiv.apply_symm_apply]
      exact hEsel n j.val j.property
    · rintro ⟨i, hi, rfl⟩
      refine ⟨MvPolynomial.X (⟨i, hi⟩ : s n), ⟨_, rfl⟩, ?_⟩
      apply (E n).injective
      simp only [RingEquiv.apply_symm_apply]
      exact (hEsel n i hi).symm
  have hPmin (n : ℕ) : P n ∈ A.minimalPrimes := by
    refine ⟨⟨hPprime n, hAP n⟩, ?_⟩
    intro Q hQ hQP
    rw [hPeq, Ideal.span_le]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    rcases hi with (rfl | ⟨k, hk, rfl⟩)
    · have hcomp : MvPolynomial.X (2*n+1) ∉ Q := by
        intro hmem
        exact hPnsel n (2*n+1) (by simp [hsodd]) (hQP hmem)
      exact (hQ.1.mem_or_mem (hQ.2 (Ideal.subset_span (by rw [hf]; exact Set.mem_range_self n)))).resolve_right hcomp
    · have hcomp : MvPolynomial.X (2*k) ∉ Q := by
        intro hmem
        exact hPnsel n (2*k) ((hseven n k).not.mpr hk) (hQP hmem)
      exact (hQ.1.mem_or_mem (hQ.2 (Ideal.subset_span (by rw [hf]; exact Set.mem_range_self k)))).resolve_left hcomp
  have hPinj : Function.Injective P := by
    intro n m hnm
    by_contra hne
    have hx : MvPolynomial.X (2*n) ∈ P n :=
      hPsel n (2*n) ((hseven n n).2 rfl)
    have hx' : MvPolynomial.X (2*n) ∈ P m := hnm ▸ hx
    exact hPnsel m (2*n) ((hseven m n).not.mpr hne) hx'
  have hcorr (n : ℕ) : ∃ q ∈ minimalPrimes (MvPolynomial ℕ ℤ ⧸ A),
      Ideal.comap (Ideal.Quotient.mk A) q = P n := by
    have hp := hPmin n
    rw [Ideal.minimalPrimes_eq_comap] at hp
    exact hp
  choose q hqmem hqcomap using hcorr
  let g : ℕ → minimalPrimes (MvPolynomial ℕ ℤ ⧸ A) := fun n => ⟨q n, hqmem n⟩
  have hginj : Function.Injective g := by
    intro n m hnm
    apply hPinj
    rw [← hqcomap n, ← hqcomap m]
    exact congrArg (fun z => Ideal.comap (Ideal.Quotient.mk A) z.val) hnm
  change Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ A))
  exact Infinite.of_injective g hginj
