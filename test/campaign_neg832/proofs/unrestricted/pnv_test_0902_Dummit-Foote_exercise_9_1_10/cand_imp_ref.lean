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
  let I : Ideal (MvPolynomial ℕ ℤ) := span (range f)
  let a (n j : ℕ) : ℤ :=
    if j = 2 * n then 1 else if j = 2 * n + 1 then 0 else if j % 2 = 0 then 0 else 1
  let e (n : ℕ) : MvPolynomial ℕ ℤ →+* ℤ :=
    MvPolynomial.eval₂Hom (RingHom.id ℤ) (a n)
  let P (n : ℕ) : Ideal (MvPolynomial ℕ ℤ) := RingHom.ker (e n)
  have ha_even_self (n : ℕ) : a n (2 * n) = 1 := by simp [a]
  have ha_odd_self (n : ℕ) : a n (2 * n + 1) = 0 := by
    simp [a]
  have ha_even_ne {n m : ℕ} (h : n ≠ m) : a n (2 * m) = 0 := by
    simp [a, Ne.symm h]
  have ha_odd_ne {n m : ℕ} (h : n ≠ m) : a n (2 * m + 1) = 1 := by
    simp [a, Ne.symm h]
  have hIP (n : ℕ) : I ≤ P n := by
    rw [show I = span (range f) from rfl]
    refine span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    rw [hf]
    change e n (MvPolynomial.X (2 * i) * MvPolynomial.X (2 * i + 1)) = 0
    by_cases h : i = n
    · subst i
      simp [e, ha_odd_self]
    · simp [e, ha_even_ne (Ne.symm h)]
  have hex : ∀ n : ℕ, ∃ q ∈ I.minimalPrimes, q ≤ P n := by
    intro n
    letI : (P n).IsPrime := RingHom.ker_isPrime (e n)
    exact Ideal.exists_minimalPrimes_le (hIP n)
  choose q hq hqP using hex
  have hq_inj : Function.Injective q := by
    intro n m hnm
    by_contra hne
    have heven_not (k : ℕ) : MvPolynomial.X (2 * k) ∉ P k := by
      simp [P, e, ha_even_self]
    have hodd_not {k l : ℕ} (hkl : k ≠ l) : MvPolynomial.X (2 * l + 1) ∉ P k := by
      simp [P, e, ha_odd_ne hkl]
    have hodd_mem (k : ℕ) : MvPolynomial.X (2 * k + 1) ∈ q k := by
      have hp : MvPolynomial.X (2 * k) * MvPolynomial.X (2 * k + 1) ∈ q k := by
        apply hq k |>.1.2
        rw [show I = span (range f) from rfl]
        apply subset_span
        exact ⟨k, by simp [hf]⟩
      rcases (Ideal.minimalPrimes_isPrime (hq k)).mem_or_mem hp with he | ho
      · exact False.elim (heven_not k (hqP k he))
      · exact ho
    have : MvPolynomial.X (2 * n + 1) ∈ q m := hnm ▸ hodd_mem n
    exact hodd_not (Ne.symm hne) (hqP m this)
  have hex' : ∀ n : ℕ, ∃ r ∈ minimalPrimes (MvPolynomial ℕ ℤ ⧸ I),
      Ideal.comap (Ideal.Quotient.mk I) r = q n := by
    intro n
    rw [Ideal.minimalPrimes_eq_comap] at hq
    simpa using hq n
  choose r hr hrq using hex'
  have hr_inj : Function.Injective r := by
    intro n m h
    apply hq_inj
    rw [← hrq n, ← hrq m, h]
  have hinf : Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ I)) :=
    Infinite.of_injective (fun n : ℕ => ⟨r n, hr n⟩) (by
      intro n m h
      apply hr_inj
      exact Subtype.ext_iff.mp h)
  simpa [I] using hinf
