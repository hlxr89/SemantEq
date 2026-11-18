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
  subst f
  let A := MvPolynomial ℕ ℤ
  let g : ℕ → ℕ → ℤ := fun n k =>
    if k = 2 * n ∨ ∃ i, i ≠ n ∧ k = 2 * i + 1 then 0 else 1
  let e : ℕ → A →+* ℤ := fun n => MvPolynomial.eval₂Hom (RingHom.id ℤ) (g n)
  let P : ℕ → Ideal A := fun n => RingHom.ker (e n)
  have hP_prime (n : ℕ) : (P n).IsPrime := by
    dsimp [P]
    exact RingHom.ker_isPrime _
  have h_even (n : ℕ) : MvPolynomial.X (2 * n) ∈ P n := by
    simp only [P, A, e, RingHom.mem_ker, MvPolynomial.eval₂Hom_X']
    simp [g]
  have h_odd_not (n : ℕ) : MvPolynomial.X (2 * n + 1) ∉ P n := by
    simp only [P, A, e, RingHom.mem_ker, MvPolynomial.eval₂Hom_X']
    have hn : ¬(2 * n + 1 = 2 * n ∨ ∃ i, i ≠ n ∧ 2 * n + 1 = 2 * i + 1) := by
      rintro (h | ⟨i, hi, h⟩) <;> omega
    simp [g, hn]
  have h_even_not {m n : ℕ} (hmn : m ≠ n) : MvPolynomial.X (2 * n) ∉ P m := by
    simp only [P, A, e, RingHom.mem_ker, MvPolynomial.eval₂Hom_X']
    have hn : ¬(2 * n = 2 * m ∨ ∃ i, i ≠ m ∧ 2 * n = 2 * i + 1) := by
      rintro (h | ⟨i, hi, h⟩) <;> omega
    rw [show g m (2 * n) = 1 by unfold g; rw [if_neg hn]]
    norm_num
  let J : Ideal A := span (range fun i : ℕ => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1))
  have hJP (n : ℕ) : J ≤ P n := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    by_cases hi : i = n
    · subst i
      exact (P n).mul_mem_right _ (h_even n)
    · apply (P n).mul_mem_left
      simp only [P, A, e, RingHom.mem_ker, MvPolynomial.eval₂Hom_X']
      simp [g, hi]
  let q : ℕ → Ideal A := fun n => Classical.choose (Ideal.exists_minimalPrimes_le (J := P n) (hJP n))
  have hq_mem (n : ℕ) : q n ∈ J.minimalPrimes :=
    (Classical.choose_spec (Ideal.exists_minimalPrimes_le (J := P n) (hJP n))).1
  have hq_le (n : ℕ) : q n ≤ P n :=
    (Classical.choose_spec (Ideal.exists_minimalPrimes_le (J := P n) (hJP n))).2
  have hq_even (n : ℕ) : MvPolynomial.X (2 * n) ∈ q n := by
    have hp : MvPolynomial.X (2 * n) * MvPolynomial.X (2 * n + 1) ∈ q n :=
      (hq_mem n).1.2 (Ideal.subset_span ⟨n, rfl⟩)
    rcases (hq_mem n).1.1.mem_or_mem hp with he | ho
    · exact he
    · exact False.elim (h_odd_not n (hq_le n ho))
  have hq_inj : Function.Injective q := by
    intro m n hmn
    by_contra hne
    have : MvPolynomial.X (2 * n) ∈ P m := hq_le m (hmn ▸ hq_even n)
    exact h_even_not hne this
  let Q := A ⧸ J
  have hex (n : ℕ) : ∃ p ∈ minimalPrimes Q, Ideal.comap (Ideal.Quotient.mk J) p = q n := by
    have := hq_mem n
    rw [Ideal.minimalPrimes_eq_comap] at this
    simpa only [Set.mem_image] using this
  let p : ℕ → minimalPrimes Q := fun n =>
    ⟨Classical.choose (hex n), (Classical.choose_spec (hex n)).1⟩
  have hp_comap (n : ℕ) : Ideal.comap (Ideal.Quotient.mk J) (p n).1 = q n :=
    (Classical.choose_spec (hex n)).2
  have hp_inj : Function.Injective p := by
    intro m n hmn
    apply hq_inj
    rw [← hp_comap m, ← hp_comap n, hmn]
  exact Infinite.of_injective p hp_inj
