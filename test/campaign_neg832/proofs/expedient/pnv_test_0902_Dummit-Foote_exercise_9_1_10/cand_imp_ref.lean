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
  subst f
  let I : Ideal (MvPolynomial ℕ ℤ) :=
    span (range (fun i : ℕ => MvPolynomial.X (2 * i) * MvPolynomial.X (2 * i + 1)))
  let g (n j : ℕ) : ℤ :=
    if j = 2 * n then 0 else if j = 2 * n + 1 then 1 else if j % 2 = 0 then 1 else 0
  let M (n : ℕ) : Ideal (MvPolynomial ℕ ℤ) :=
    RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id ℤ) (g n))
  have hM (n : ℕ) : (M n).IsPrime := by
    dsimp [M]
    exact RingHom.ker_isPrime _
  have hle (n : ℕ) : I ≤ M n := by
    dsimp only [I]
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    dsimp only [M]
    change MvPolynomial.eval₂Hom (RingHom.id ℤ) (g n)
      (MvPolynomial.X (2 * i) * MvPolynomial.X (2 * i + 1)) = 0
    simp [g]
  let q (n : ℕ) : Ideal (MvPolynomial ℕ ℤ) :=
    Classical.choose (@Ideal.exists_minimalPrimes_le _ _ I (M n) (hM n) (hle n))
  have hqmem (n : ℕ) : q n ∈ I.minimalPrimes :=
    (Classical.choose_spec
      (@Ideal.exists_minimalPrimes_le _ _ I (M n) (hM n) (hle n))).1
  have hqle (n : ℕ) : q n ≤ M n :=
    (Classical.choose_spec
      (@Ideal.exists_minimalPrimes_le _ _ I (M n) (hM n) (hle n))).2
  have hXmem (n : ℕ) : MvPolynomial.X (2 * n) ∈ q n := by
    have hp : MvPolynomial.X (2 * n) * MvPolynomial.X (2 * n + 1) ∈ q n :=
      hqmem n |>.1.2 (Ideal.subset_span (Set.mem_range_self n))
    rcases (hqmem n).1.1.mem_or_mem hp with he | ho
    · exact he
    · exfalso
      have := hqle n ho
      dsimp only [M] at this
      rw [RingHom.mem_ker] at this
      simpa [g] using this
  have hXnot (m n : ℕ) (h : m ≠ n) : MvPolynomial.X (2 * m) ∉ q n := by
    intro hx
    have := hqle n hx
    dsimp only [M] at this
    rw [RingHom.mem_ker] at this
    have hne : 2 * m ≠ 2 * n := by omega
    simpa [g, hne] using this
  let qs (n : ℕ) : I.minimalPrimes := ⟨q n, hqmem n⟩
  have hqinj : Function.Injective qs := by
    intro m n e
    have e' := congrArg Subtype.val e
    change q m = q n at e'
    by_contra h
    have hm : MvPolynomial.X (2 * m) ∈ q n := by
      rw [← e']
      exact hXmem m
    exact hXnot m n h hm
  haveI : Infinite I.minimalPrimes := Infinite.of_injective qs hqinj
  let c : minimalPrimes (MvPolynomial ℕ ℤ ⧸ I) → I.minimalPrimes := fun p =>
    ⟨Ideal.comap (Ideal.Quotient.mk I) p.1, by
      rw [Ideal.minimalPrimes_eq_comap]
      exact ⟨p.1, p.2, rfl⟩⟩
  have hc : Function.Surjective c := by
    rintro ⟨p, hp⟩
    rw [Ideal.minimalPrimes_eq_comap] at hp
    obtain ⟨P, hP, rfl⟩ := hp
    exact ⟨⟨P, hP⟩, rfl⟩
  change Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ I))
  exact Infinite.of_surjective c hc
