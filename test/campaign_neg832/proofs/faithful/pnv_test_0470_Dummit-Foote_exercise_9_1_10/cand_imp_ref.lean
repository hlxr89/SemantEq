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
  obtain ⟨P, hP, _⟩ := dummy_assumed
  let A := Polynomial ℤ ⧸ P 0
  letI : IsDomain A := (Ideal.Quotient.isDomain_iff_prime (P 0)).2 (hP 0)
  let value (n j : ℕ) : A :=
    if j % 2 = 0 then
      if j / 2 = n then 0 else 1
    else
      if j / 2 = n then 1 else 0
  let ev (n : ℕ) : MvPolynomial ℕ ℤ →+* A :=
    MvPolynomial.eval₂Hom ((Ideal.Quotient.mk (P 0)).comp Polynomial.C) (value n)
  let J : Ideal (MvPolynomial ℕ ℤ) := span (range f)
  have hJker (n : ℕ) : J ≤ RingHom.ker (ev n) := by
    apply span_le.2
    rintro _ ⟨k, rfl⟩
    rw [hf]
    simp only [ev, map_mul, MvPolynomial.eval₂_X]
    simp only [value]
    by_cases hkn : k = n
    · subst k
      simp
    · have h2kn : 2 * k / 2 ≠ n := by omega
      have h2k1n : (2 * k + 1) / 2 ≠ n := by omega
      simp [h2kn, h2k1n]
  have hker_prime (n : ℕ) : (RingHom.ker (ev n)).IsPrime := RingHom.ker_isPrime (ev n)
  let Q (n : ℕ) : Ideal (MvPolynomial ℕ ℤ) :=
    Classical.choose (Ideal.exists_minimalPrimes_le (hJker n))
  have hQmin (n : ℕ) : Q n ∈ J.minimalPrimes :=
    (Classical.choose_spec (Ideal.exists_minimalPrimes_le (hJker n))).1
  have hQle (n : ℕ) : Q n ≤ RingHom.ker (ev n) :=
    (Classical.choose_spec (Ideal.exists_minimalPrimes_le (hJker n))).2
  have heven_mem (n : ℕ) : MvPolynomial.X (2 * n) ∈ Q n := by
    have hprod : MvPolynomial.X (2 * n) * MvPolynomial.X (2 * n + 1) ∈ Q n := by
      exact hQmin n |>.1.2 (by
        apply subset_span
        exact ⟨n, by simp [hf]⟩)
    rcases (hQmin n).1.1.mem_or_mem hprod with h | h
    · exact h
    · have : MvPolynomial.X (2 * n + 1) ∈ RingHom.ker (ev n) := hQle n h
      have hdiv : (2 * n + 1) / 2 = n := by omega
      exfalso
      simpa [RingHom.mem_ker, ev, value, hdiv] using this
  have heven_not_mem {n k : ℕ} (hnk : n ≠ k) : MvPolynomial.X (2 * n) ∉ Q k := by
    intro h
    have : MvPolynomial.X (2 * n) ∈ RingHom.ker (ev k) := hQle k h
    have heq : n = k := by
      simpa [RingHom.mem_ker, ev, value] using this
    exact hnk heq
  have hQinj : Function.Injective Q := by
    intro n k h
    by_contra hnk
    exact heven_not_mem hnk (h ▸ heven_mem n)
  have hQlift (n : ℕ) : ∃ p ∈ minimalPrimes (MvPolynomial ℕ ℤ ⧸ J),
      Ideal.comap (Ideal.Quotient.mk J) p = Q n := by
    rw [Ideal.minimalPrimes_eq_comap] at hQmin
    simpa only [eq_comm] using hQmin n
  let q (n : ℕ) : minimalPrimes (MvPolynomial ℕ ℤ ⧸ J) :=
    ⟨Classical.choose (hQlift n), (Classical.choose_spec (hQlift n)).1⟩
  have hq_comap (n : ℕ) : Ideal.comap (Ideal.Quotient.mk J) (q n) = Q n :=
    (Classical.choose_spec (hQlift n)).2
  have hqinj : Function.Injective q := by
    intro n k h
    apply hQinj
    rw [← hq_comap n, ← hq_comap k, h]
  have : Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ J)) :=
    Infinite.of_injective q hqinj
  simpa [J] using this
