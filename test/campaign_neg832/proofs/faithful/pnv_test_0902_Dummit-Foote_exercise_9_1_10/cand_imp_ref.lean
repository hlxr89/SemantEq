import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : (Infinite (Set.range (fun (n : ℕ) => Ico (n*2) (n*2 + 1)))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_1_10 {f : ℕ → MvPolynomial ℕ ℤ}
  (hf : f = λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)):
  Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) := by
  classical
  letI := dummy_assumed
  let I : Ideal (MvPolynomial ℕ ℤ) := span (range f)
  let a : ℕ → ℕ → ℤ := fun n j =>
    if Even j then (if j / 2 = n then 0 else 1)
    else (if j / 2 = n then 1 else 0)
  let e : ℕ → MvPolynomial ℕ ℤ →+* ℤ := fun n =>
    MvPolynomial.eval₂Hom (RingHom.id ℤ) (a n)
  have ha_even (n i : ℕ) : a n (2 * i) = if i = n then 0 else 1 := by
    simp [a, Nat.mul_div_cancel_left]
  have ha_odd (n i : ℕ) : a n (2 * i + 1) = if i = n then 1 else 0 := by
    simp [a]
    omega
  have hIK (n : ℕ) : I ≤ RingHom.ker (e n) := by
    change span (range f) ≤ RingHom.ker (e n)
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [hf]
    change e n (MvPolynomial.X (2 * i) * MvPolynomial.X (2 * i + 1)) = 0
    rw [map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    simp only [e, ha_even, ha_odd]
    split_ifs <;> simp
  have hex (n : ℕ) :
      ∃ p ∈ I.minimalPrimes, p ≤ RingHom.ker (e n) := by
    letI : (RingHom.ker (e n)).IsPrime := RingHom.ker_isPrime (e n)
    exact Ideal.exists_minimalPrimes_le (hIK n)
  let p : ℕ → Ideal (MvPolynomial ℕ ℤ) := fun n =>
    Classical.choose (hex n)
  have hp_mem (n : ℕ) : p n ∈ I.minimalPrimes :=
    (Classical.choose_spec (hex n)).1
  have hp_le (n : ℕ) : p n ≤ RingHom.ker (e n) :=
    (Classical.choose_spec (hex n)).2
  have hp_even_mem (n : ℕ) : MvPolynomial.X (2 * n) ∈ p n := by
    have hprod : MvPolynomial.X (2 * n) * MvPolynomial.X (2 * n + 1) ∈ p n := by
      apply hp_mem n |>.1.2
      apply Ideal.subset_span
      rw [hf]
      exact Set.mem_range_self n
    have hodd : MvPolynomial.X (2 * n + 1) ∉ p n := by
      intro h
      have := hp_le n h
      rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_X'] at this
      simpa [e, ha_odd] using this
    exact (Ideal.minimalPrimes_isPrime (hp_mem n)).2 hprod |>.resolve_right hodd
  have hp_even_not_mem {m n : ℕ} (h : n ≠ m) : MvPolynomial.X (2 * n) ∉ p m := by
    intro hx
    have := hp_le m hx
    rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_X'] at this
    simpa [e, ha_even, h] using this
  have hp_inj : Function.Injective p := by
    intro m n hmn
    by_contra h
    have hx := hp_even_mem m
    rw [hmn] at hx
    exact hp_even_not_mem (m := n) (n := m) h hx
  let g : ℕ → Set ℕ := fun n => Ico (n * 2) (n * 2 + 1)
  have hg_inj : Function.Injective g := by
    intro m n hmn
    have hm : m * 2 ∈ g m := by simp [g]
    rw [hmn] at hm
    simp [g] at hm
    omega
  let idx : Set.range g → ℕ := fun x => Classical.choose x.2
  have hidx_spec (x : Set.range g) : g (idx x) = x.1 :=
    Classical.choose_spec x.2
  have hidx_inj : Function.Injective idx := by
    intro x y hxy
    apply Subtype.ext
    rw [← hidx_spec x, ← hidx_spec y, hxy]
  haveI hInfP : Infinite I.minimalPrimes :=
    Infinite.of_injective
      (fun x : Set.range g => (⟨p (idx x), hp_mem (idx x)⟩ : I.minimalPrimes))
      (fun _ _ h => hidx_inj (hp_inj (Subtype.ext_iff.mp h)))
  have hpre (q : I.minimalPrimes) :
      ∃ Q : minimalPrimes (MvPolynomial ℕ ℤ ⧸ I),
        Ideal.comap (Ideal.Quotient.mk I) Q.1 = q.1 := by
    have hq : q.1 ∈ Ideal.comap (Ideal.Quotient.mk I) ''
        minimalPrimes (MvPolynomial ℕ ℤ ⧸ I) := by
      rw [← Ideal.minimalPrimes_eq_comap]
      exact q.2
    rcases hq with ⟨Q, hQ, hEq⟩
    exact ⟨⟨Q, hQ⟩, hEq⟩
  let liftP : I.minimalPrimes → minimalPrimes (MvPolynomial ℕ ℤ ⧸ I) := fun q =>
    Classical.choose (hpre q)
  have hlift_inj : Function.Injective liftP := by
    intro q r hqr
    apply Subtype.ext
    have hq := Classical.choose_spec (hpre q)
    have hr := Classical.choose_spec (hpre r)
    change Ideal.comap (Ideal.Quotient.mk I) (liftP q).1 = q.1 at hq
    change Ideal.comap (Ideal.Quotient.mk I) (liftP r).1 = r.1 at hr
    rw [hqr] at hq
    exact hq.symm.trans hr
  haveI : Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ I)) :=
    Infinite.of_injective liftP hlift_inj
  simpa [I]
