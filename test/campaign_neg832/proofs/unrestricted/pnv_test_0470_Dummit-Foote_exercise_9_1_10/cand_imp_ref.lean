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
  subst f
  let g : ℕ → ℕ → MvPolynomial ℕ ℤ := fun n k =>
    if (k % 2 = 0 ↔ k / 2 = n) then 0 else MvPolynomial.X k
  let φ : ℕ → MvPolynomial ℕ ℤ →+* MvPolynomial ℕ ℤ := fun n =>
    MvPolynomial.eval₂Hom MvPolynomial.C (g n)
  let I : Ideal (MvPolynomial ℕ ℤ) :=
    span (range (fun i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)))
  let J : ℕ → Ideal (MvPolynomial ℕ ℤ) := fun n => RingHom.ker (φ n)
  have hφ_even (n i : ℕ) : φ n (MvPolynomial.X (2*i)) =
      if i = n then 0 else MvPolynomial.X (2*i) := by
    simp [φ, g]
  have hφ_odd (n i : ℕ) : φ n (MvPolynomial.X (2*i+1)) =
      if i = n then MvPolynomial.X (2*i+1) else 0 := by
    have hi : (2*i+1) / 2 = i := by omega
    simp [φ, g, hi]
  have hJprime (n : ℕ) : (J n).IsPrime := by
    dsimp [J]
    exact RingHom.ker_isPrime _
  have hIJ (n : ℕ) : I ≤ J n := by
    change span (range (fun i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1))) ≤
      RingHom.ker (φ n)
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change φ n (MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)) = 0
    rw [map_mul, hφ_even, hφ_odd]
    by_cases h : i = n <;> simp [h]
  have hJminimal (n : ℕ) : J n ∈ I.minimalPrimes := by
    refine ⟨⟨hJprime n, hIJ n⟩, ?_⟩
    intro q hq hqJ
    have hprod (i : ℕ) :
        MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1) ∈ q := by
      apply hq.2
      exact Ideal.subset_span ⟨i, rfl⟩
    have hEvenQ : MvPolynomial.X (2*n) ∈ q := by
      rcases hq.1.mem_or_mem (hprod n) with heven | hodd
      · exact heven
      · exfalso
        have := hqJ hodd
        change MvPolynomial.X (2*n+1) ∈ RingHom.ker (φ n) at this
        rw [RingHom.mem_ker, hφ_odd] at this
        simpa using this
    have hOddQ (i : ℕ) (hi : i ≠ n) : MvPolynomial.X (2*i+1) ∈ q := by
      rcases hq.1.mem_or_mem (hprod i) with heven | hodd
      · exfalso
        have := hqJ heven
        change MvPolynomial.X (2*i) ∈ RingHom.ker (φ n) at this
        rw [RingHom.mem_ker, hφ_even] at this
        simp [hi] at this
      · exact hodd
    have hXQ (k : ℕ) (hk : (k % 2 = 0 ↔ k / 2 = n)) : MvPolynomial.X k ∈ q := by
      by_cases he : k % 2 = 0
      · have hn : k / 2 = n := hk.mp he
        rw [show k = 2*n by omega]
        exact hEvenQ
      · have hn : k / 2 ≠ n := by
          intro hn
          exact he (hk.mpr hn)
        have hform : k = 2 * (k / 2) + 1 := by omega
        rw [hform]
        exact hOddQ (k / 2) hn
    have hdiff (p : MvPolynomial ℕ ℤ) : p - φ n p ∈ q := by
      induction p using MvPolynomial.induction_on with
      | C a => simp [φ]
      | add p r hp hr =>
          rw [map_add]
          convert q.add_mem hp hr using 1 <;> ring
      | mul_X p k hp =>
          rw [map_mul]
          by_cases hk : (k % 2 = 0 ↔ k / 2 = n)
          · simp only [φ, MvPolynomial.eval₂Hom_X', g, if_pos hk, mul_zero, sub_zero]
            exact q.mul_mem_left p (hXQ k hk)
          · simp only [φ, MvPolynomial.eval₂Hom_X', g, if_neg hk]
            rw [← sub_mul]
            exact q.mul_mem_right _ hp
    have hJq : J n ≤ q := by
      intro p hp
      change p ∈ RingHom.ker (φ n) at hp
      rw [RingHom.mem_ker] at hp
      simpa [hp] using hdiff p
    exact hJq
  have hJinj : Function.Injective J := by
    intro n m hnm
    by_contra hne
    have hx : MvPolynomial.X (2*n) ∈ J n := by
      change φ n (MvPolynomial.X (2*n)) = 0
      simp [hφ_even]
    rw [hnm] at hx
    change φ m (MvPolynomial.X (2*n)) = 0 at hx
    rw [hφ_even] at hx
    simp [hne] at hx
  have hexists (n : ℕ) :
      ∃ p ∈ minimalPrimes (MvPolynomial ℕ ℤ ⧸ I),
        Ideal.comap (Ideal.Quotient.mk I) p = J n := by
    have hn := hJminimal n
    rw [Ideal.minimalPrimes_eq_comap] at hn
    exact hn
  let Q : ℕ → Ideal (MvPolynomial ℕ ℤ ⧸ I) := fun n => (hexists n).choose
  have hQmem (n : ℕ) : Q n ∈ minimalPrimes (MvPolynomial ℕ ℤ ⧸ I) :=
    (hexists n).choose_spec.1
  have hQcomap (n : ℕ) : Ideal.comap (Ideal.Quotient.mk I) (Q n) = J n :=
    (hexists n).choose_spec.2
  have hQinj : Function.Injective Q := by
    intro n m hnm
    apply hJinj
    rw [← hQcomap n, ← hQcomap m, hnm]
  change Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ I))
  exact Infinite.of_injective (fun n => ⟨Q n, hQmem n⟩) (fun n m h => hQinj (congrArg Subtype.val h))
