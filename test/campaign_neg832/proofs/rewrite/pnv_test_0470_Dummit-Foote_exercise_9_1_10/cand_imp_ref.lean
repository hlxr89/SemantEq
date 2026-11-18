import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ∃ (P : ℕ → Ideal (Polynomial (ℤ))), (∀ n, Ideal.IsPrime (P n)) ∧ (∀ n m, n ≠ m → P n ≠ P m) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_1_10 {f : ℕ → MvPolynomial ℕ ℤ}
  (hf : f = λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)):
  Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) := by
  rcases dummy_assumed with ⟨P, hPprime, hPne⟩
  let β := range P
  let E : ℕ → β := fun n => ⟨P n, ⟨n, rfl⟩⟩
  have hPinj : Function.Injective P :=
    Function.injective_iff_pairwise_ne.mpr hPne
  have hEinj : Function.Injective E := by
    intro n m heq
    exact hPinj (congrArg Subtype.val heq)
  letI : Infinite β := Infinite.of_injective E hEinj
  let index : β → ℕ := fun p => Classical.choose p.property
  have hindex (p : β) : P (index p) = p.1 := Classical.choose_spec p.property
  let g : ℕ → ℕ → ℤ := fun n k =>
    if k = 2*n+1 then 1 else if Odd k then 0 else if k = 2*n then 0 else 1
  let φ : ℕ → MvPolynomial ℕ ℤ →+* ℤ :=
    fun n => MvPolynomial.eval₂Hom (RingHom.id ℤ) (g n)
  have hodd (i : ℕ) : Odd (2*i+1) := ⟨i, rfl⟩
  have heven (i : ℕ) : ¬ Odd (2*i) := by
    exact Nat.not_odd_iff_even.mpr ⟨i, two_mul i⟩
  have hφ (n i : ℕ) : φ n (MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)) = 0 := by
    by_cases h : i = n
    · subst n
      simp only [φ, map_mul, MvPolynomial.eval₂Hom_X']
      simp only [g, hodd, heven, if_true, if_false]
      split <;> simp_all
    · simp only [φ, map_mul, MvPolynomial.eval₂Hom_X']
      have hne : 2*i+1 ≠ 2*n+1 := by
        intro he
        exact h (Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ 1) (Nat.add_right_cancel he))
      simp only [g, hne, hodd, if_false, if_true, mul_zero]
  have hspan (n : ℕ) : span (range f) ≤ RingHom.ker (φ n) := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    change (φ n) (f i) = 0
    rw [hf]
    exact hφ n i
  let ψ : ℕ → (MvPolynomial ℕ ℤ ⧸ span (range f)) →+* ℤ := fun n =>
    Ideal.Quotient.lift (span (range f)) (φ n)
      (fun a ha => RingHom.mem_ker.mp (hspan n ha))
  have hψprime (n : ℕ) : (RingHom.ker (ψ n)).IsPrime := RingHom.ker_isPrime _
  have hex (n : ℕ) : ∃ q ∈ minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f)),
      q ≤ RingHom.ker (ψ n) := by
    letI := hψprime n
    exact Ideal.exists_minimalPrimes_le bot_le
  let q : ℕ → Ideal (MvPolynomial ℕ ℤ ⧸ span (range f)) := fun n => (hex n).choose
  have hqmem (n : ℕ) : q n ∈ minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f)) :=
    (hex n).choose_spec.1
  have hqle (n : ℕ) : q n ≤ RingHom.ker (ψ n) := (hex n).choose_spec.2
  have hqin (n : ℕ) :
      (Ideal.Quotient.mk (span (range f))) (MvPolynomial.X (2*n)) ∈ q n := by
    have hprod : (Ideal.Quotient.mk (span (range f)))
        (MvPolynomial.X (2*n) * MvPolynomial.X (2*n+1)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.subset_span
      exact ⟨n, hf.symm ▸ rfl⟩
    have hp : ((Ideal.Quotient.mk (span (range f))) (MvPolynomial.X (2*n))) *
        ((Ideal.Quotient.mk (span (range f))) (MvPolynomial.X (2*n+1))) ∈ q n := by
      rw [← map_mul, hprod]
      exact (q n).zero_mem
    rcases (hqmem n).1.1.mem_or_mem hp with hevenmem | hoddmem
    · exact hevenmem
    · have hk := hqle n hoddmem
      rw [RingHom.mem_ker] at hk
      simp only [ψ, Ideal.Quotient.lift_mk, φ, MvPolynomial.eval₂Hom_X'] at hk
      simp only [g, if_pos rfl, one_ne_zero] at hk
  have hqout (n m : ℕ) (h : n ≠ m) :
      (Ideal.Quotient.mk (span (range f))) (MvPolynomial.X (2*n)) ∉ q m := by
    intro hmem
    have hk := hqle m hmem
    rw [RingHom.mem_ker] at hk
    simp only [ψ, Ideal.Quotient.lift_mk, φ, MvPolynomial.eval₂Hom_X'] at hk
    have hne : 2*n ≠ 2*m := fun he =>
      h (Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ 1) he)
    have hpar : 2*n ≠ 2*m+1 := fun he => heven n (he.symm ▸ hodd m)
    simp only [g, hpar, hne, heven, if_false, one_ne_zero] at hk
  let Q : β → minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f)) :=
    fun p => ⟨q (index p), hqmem (index p)⟩
  have hqinj : Function.Injective q :=
    Function.injective_iff_pairwise_ne.mpr fun n m hne heq =>
      hqout n m hne (heq ▸ hqin n)
  have hQinj : Function.Injective Q := by
    intro p r heq
    have hi : index p = index r := hqinj (Subtype.ext_iff.mp heq)
    apply Subtype.ext
    change p.1 = r.1
    rw [← hindex p, hi, hindex r]
  exact Infinite.of_injective Q hQinj
