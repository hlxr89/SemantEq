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
  let A := MvPolynomial ℕ ℤ
  let g : ℕ → ℕ → A := fun n i =>
    if i = 2 * n then 0
    else if i = 2 * n + 1 then MvPolynomial.X i
    else if Odd i then 0
    else MvPolynomial.X i
  let e : ℕ → A →+* A := fun n => MvPolynomial.eval₂Hom MvPolynomial.C (g n)
  let P : ℕ → Ideal A := fun n => RingHom.ker (e n)
  have g_even_self (n : ℕ) : g n (2 * n) = 0 := by
    simp [g]
  have g_odd_self (n : ℕ) : g n (2 * n + 1) = MvPolynomial.X (2 * n + 1) := by
    simp [g]
  have g_even_ne {n k : ℕ} (hkn : k ≠ n) : g n (2 * k) = MvPolynomial.X (2 * k) := by
    simp only [g, if_neg (by omega : 2 * k ≠ 2 * n), if_neg (by omega : 2 * k ≠ 2 * n + 1)]
    simp
  have g_odd_ne {n k : ℕ} (hkn : k ≠ n) : g n (2 * k + 1) = 0 := by
    simp only [g, if_neg (by omega : 2 * k + 1 ≠ 2 * n), if_neg (by omega : 2 * k + 1 ≠ 2 * n + 1)]
    simp
  have heval_X (n i : ℕ) : e n (MvPolynomial.X i) = g n i := by
    change (MvPolynomial.eval₂Hom MvPolynomial.C (g n)) (MvPolynomial.X i) = g n i
    exact MvPolynomial.eval₂Hom_X' MvPolynomial.C (g n) i
  have x_mem_P_iff (n i : ℕ) : MvPolynomial.X i ∈ P n ↔ g n i = 0 := by
    change e n (MvPolynomial.X i) = 0 ↔ _
    rw [heval_X]
  let I : Ideal A := span (range (fun i : ℕ => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)))
  have hIP (n : ℕ) : I ≤ P n := by
    change span (range (fun i : ℕ => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1))) ≤ P n
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    by_cases hkn : k = n
    · subst k
      exact (P n).mul_mem_right _ ((x_mem_P_iff n _).2 (g_even_self n))
    · exact (P n).mul_mem_left _ ((x_mem_P_iff n _).2 (g_odd_ne hkn))
  have hPprime (n : ℕ) : (P n).IsPrime := by
    exact RingHom.ker_isPrime (e n)
  let B : ℕ → Ideal A := fun n =>
    Classical.choose (Ideal.exists_minimalPrimes_le (I := I) (J := P n) (hIP n))
  have hBmin (n : ℕ) : B n ∈ I.minimalPrimes :=
    (Classical.choose_spec (Ideal.exists_minimalPrimes_le (I := I) (J := P n) (hIP n))).1
  have hBleP (n : ℕ) : B n ≤ P n :=
    (Classical.choose_spec (Ideal.exists_minimalPrimes_le (I := I) (J := P n) (hIP n))).2
  have hB_selected (n : ℕ) : MvPolynomial.X (2 * n) ∈ B n := by
    have hprod : MvPolynomial.X (2 * n) * MvPolynomial.X (2 * n + 1) ∈ B n :=
      (hBmin n).1.2 (by
        change MvPolynomial.X (2 * n) * MvPolynomial.X (2 * n + 1) ∈
          span (range (fun i : ℕ => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)))
        exact Ideal.mem_span_range_self (f := fun i : ℕ =>
          MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)) (x := n))
    rcases (hBmin n).1.1.mem_or_mem hprod with heven | hodd
    · exact heven
    · exfalso
      have : MvPolynomial.X (2 * n + 1) ∈ P n := hBleP n hodd
      rw [x_mem_P_iff, g_odd_self] at this
      exact MvPolynomial.X_ne_zero _ this
  have hB_injective : Function.Injective B := by
    intro n m hnm
    by_contra hne
    have hx : MvPolynomial.X (2 * n) ∈ B m := hnm ▸ hB_selected n
    have hx' : MvPolynomial.X (2 * n) ∈ P m := hBleP m hx
    rw [x_mem_P_iff, g_even_ne hne] at hx'
    exact MvPolynomial.X_ne_zero _ hx'
  have hcomap_bot : Ideal.comap (Ideal.Quotient.mk I) (⊥ : Ideal (A ⧸ I)) = I := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  let Q : ℕ → minimalPrimes (A ⧸ I) := fun n =>
    ⟨Classical.choose (Ideal.exists_minimalPrimes_comap_eq (I := (⊥ : Ideal (A ⧸ I)))
        (Ideal.Quotient.mk I) (B n) (by rw [hcomap_bot]; exact hBmin n)),
      (Classical.choose_spec (Ideal.exists_minimalPrimes_comap_eq (I := (⊥ : Ideal (A ⧸ I)))
        (Ideal.Quotient.mk I) (B n) (by rw [hcomap_bot]; exact hBmin n))).1⟩
  have hQ_comap (n : ℕ) : Ideal.comap (Ideal.Quotient.mk I) (Q n).1 = B n :=
    (Classical.choose_spec (Ideal.exists_minimalPrimes_comap_eq (I := (⊥ : Ideal (A ⧸ I)))
      (Ideal.Quotient.mk I) (B n) (by rw [hcomap_bot]; exact hBmin n))).2
  have hQ_injective : Function.Injective Q := by
    intro n m hnm
    apply hB_injective
    rw [← hQ_comap n, ← hQ_comap m, hnm]
  exact Infinite.of_injective Q hQ_injective
