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
  classical
  subst f
  have span_X_isPrime (s : Set ℕ) :
      (Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial ℕ ℤ))).IsPrime := by
    let φ : MvPolynomial ℕ ℤ →+* MvPolynomial {i // i ∉ s} ℤ :=
      MvPolynomial.eval₂Hom (MvPolynomial.C : ℤ →+* MvPolynomial {i // i ∉ s} ℤ)
        (fun i => if hi : i ∈ s then 0 else MvPolynomial.X ⟨i, hi⟩)
    let ψ : MvPolynomial {i // i ∉ s} ℤ →+* MvPolynomial ℕ ℤ :=
      (MvPolynomial.rename (R := ℤ) (fun i : {i // i ∉ s} => (i : ℕ))).toRingHom
    have hdiff : ∀ p : MvPolynomial ℕ ℤ,
        p - ψ (φ p) ∈ Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial ℕ ℤ)) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a => simp [φ, ψ]
      | add p q hp hq =>
          simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            Ideal.add_mem _ hp hq
      | mul_X p i hp =>
          by_cases hi : i ∈ s
          · have hXi : MvPolynomial.X i ∈
                Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial ℕ ℤ)) :=
              Ideal.subset_span ⟨i, hi, rfl⟩
            simpa [φ, ψ, hi] using
              Ideal.mul_mem_left
                (Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial ℕ ℤ))) p hXi
          · have hm := Ideal.mul_mem_right (MvPolynomial.X i) _ hp
            simpa [φ, ψ, hi, sub_mul] using hm
    have hker : RingHom.ker φ =
        Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial ℕ ℤ)) := by
      apply le_antisymm
      · intro p hp
        have hz : φ p = 0 := hp
        simpa [hz] using hdiff p
      · rw [Ideal.span_le]
        rintro _ ⟨i, hi, rfl⟩
        simp [RingHom.mem_ker, φ, hi]
    rw [← hker]
    exact RingHom.ker_isPrime φ
  have X_mem_span (s : Set ℕ) (j : ℕ) :
      MvPolynomial.X j ∈ Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial ℕ ℤ)) ↔
        j ∈ s := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    simp [MvPolynomial.support_X, Finsupp.single_apply]
  let s : ℕ → Set ℕ := fun n => {j | j = 2*n+1 ∨ (Even j ∧ j ≠ 2*n)}
  let P : ℕ → Ideal (MvPolynomial ℕ ℤ) := fun n =>
    Ideal.span (MvPolynomial.X '' s n : Set (MvPolynomial ℕ ℤ))
  let I : Ideal (MvPolynomial ℕ ℤ) :=
    Ideal.span (Set.range fun i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1))
  have hseven (n i : ℕ) : 2*i ∈ s n ↔ i ≠ n := by
    simp [s, even_iff_two_dvd]
    omega
  have hsodd (n i : ℕ) : 2*i+1 ∈ s n ↔ i = n := by
    simp [s, even_iff_two_dvd]
  have hX (n j : ℕ) : MvPolynomial.X j ∈ P n ↔ j ∈ s n := by
    exact X_mem_span (s n) j
  have hp (n : ℕ) : (P n).IsPrime := by
    exact span_X_isPrime (s n)
  have hIP (n : ℕ) : I ≤ P n := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hin : i = n
    · exact Ideal.mul_mem_left _ _ ((hX n (2*i+1)).2 ((hsodd n i).2 hin))
    · exact Ideal.mul_mem_right _ _ ((hX n (2*i)).2 ((hseven n i).2 hin))
  have hmin (n : ℕ) : P n ∈ I.minimalPrimes := by
    refine ⟨⟨hp n, hIP n⟩, ?_⟩
    intro q hq hqP
    apply Ideal.span_le.2
    rintro _ ⟨j, hj, rfl⟩
    rcases hj with (rfl | ⟨hj_even, hj_ne⟩)
    · have hprod : MvPolynomial.X (2*n) * MvPolynomial.X (2*n+1) ∈ q :=
        hq.2 (Ideal.subset_span ⟨n, rfl⟩)
      rcases hq.1.mem_or_mem hprod with heven | hodd
      · exact False.elim ((not_congr (hX n (2*n))).2 (by simp [hseven]) (hqP heven))
      · exact hodd
    · obtain ⟨i, rfl⟩ := hj_even
      have hin : i ≠ n := by omega
      have hprod : MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1) ∈ q :=
        hq.2 (Ideal.subset_span ⟨i, rfl⟩)
      rcases hq.1.mem_or_mem hprod with heven | hodd
      · simpa [two_mul] using heven
      · exact False.elim
          ((not_congr (hX n (2*i+1))).2 (by simp [hsodd, hin]) (hqP hodd))
  let Q : ℕ → Ideal (MvPolynomial ℕ ℤ ⧸ I) := fun n =>
    (P n).map (Ideal.Quotient.mk I)
  have hQmin (n : ℕ) : Q n ∈ minimalPrimes (MvPolynomial ℕ ℤ ⧸ I) := by
    change (P n).map (Ideal.Quotient.mk I) ∈
      (⊥ : Ideal (MvPolynomial ℕ ℤ ⧸ I)).minimalPrimes
    rw [← Ideal.map_quotient_self I,
      Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective]
    refine ⟨P n, ?_, rfl⟩
    simpa using hmin n
  have hPinj : Function.Injective P := by
    intro n m hnm
    by_contra hne
    have hx : MvPolynomial.X (2*n+1) ∈ P n := (hX n _).2 ((hsodd n n).2 rfl)
    have hx' : MvPolynomial.X (2*n+1) ∈ P m := hnm ▸ hx
    have : n = m := (hsodd m n).1 ((hX m _).1 hx')
    exact hne this
  apply Infinite.of_injective
    (fun n => (⟨Q n, hQmin n⟩ : minimalPrimes (MvPolynomial ℕ ℤ ⧸ I)))
  intro n m hnm
  apply hPinj
  have hc := congrArg (fun J : Ideal (MvPolynomial ℕ ℤ ⧸ I) =>
    J.comap (Ideal.Quotient.mk I)) (congrArg Subtype.val hnm)
  simpa only [Q, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr (hIP n),
    sup_eq_left.mpr (hIP m)] using hc
