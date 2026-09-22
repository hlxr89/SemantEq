import Mathlib

open Filter Topology
open Polynomial

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1991_a3_solution : Set (Polynomial ℝ) := {p : Polynomial ℝ | p.degree = 2 ∧ (∃ r1 r2 : ℝ, r1 ≠ r2 ∧ p.eval r1 = 0 ∧ p.eval r2 = 0)}

def putnam_1991_a3_solution_cand : Set (Polynomial ℝ) :=
  {p | ∃ c a b : ℝ, c ≠ 0 ∧ a < b ∧ p = C c * (X - C a) * (X - C b)}

-- ===== assumed statement (antecedent) =====
theorem putnam_1991_a3_assumed (n : ℕ) (hn : 2 ≤ n) (p : Polynomial ℝ) (hdeg : p.natDegree = n) :
    (∃ r : ℕ → ℝ,
      (∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i < j → r i < r j) ∧
      (∀ i ∈ Finset.Icc 1 n, p.eval (r i) = 0) ∧
      (∀ i ∈ Finset.Icc 1 (n - 1), (derivative p).eval ((r i + r (i + 1)) / 2) = 0)) ↔
    p ∈ putnam_1991_a3_solution_cand := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1991_a3_refs
  (p : Polynomial ℝ)
  (n : ℕ)
  (hn : n = p.degree)
  (hge : n ≥ 2) :
  p ∈ putnam_1991_a3_solution ↔
    (∃ r : ℕ → ℝ, (∀ i : Fin (n - 1), r i < r (i + 1)) ∧
    (∀ i : Fin n, p.eval (r i) = 0) ∧
    (∀ i : Fin (n - 1), (Polynomial.derivative p).eval ((r i + r (i + 1)) / 2) = 0)) := by
  have hp0 : p ≠ 0 := by
    intro hp
    subst p
    simp at hn
  have hdeg : p.natDegree = n :=
    (Polynomial.degree_eq_iff_natDegree_eq hp0).mp hn.symm
  have hcand := putnam_1991_a3_assumed n hge p hdeg
  have hsol : p ∈ putnam_1991_a3_solution ↔ p ∈ putnam_1991_a3_solution_cand := by
    constructor
    · rintro ⟨hd, r₁, r₂, hr, h₁, h₂⟩
      have hd' : p.natDegree = 2 := (Polynomial.degree_eq_iff_natDegree_eq hp0).mp hd
      have hdvd₁ : X - C r₁ ∣ p := Polynomial.dvd_iff_isRoot.mpr h₁
      have hdvd₂ : X - C r₂ ∣ p := Polynomial.dvd_iff_isRoot.mpr h₂
      have hcop : IsCoprime (X - C r₁ : Polynomial ℝ) (X - C r₂) :=
        Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hr).isUnit
      have hdvd : (X - C r₁) * (X - C r₂) ∣ p := hcop.mul_dvd hdvd₁ hdvd₂
      have heq := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
        ((Polynomial.monic_X_sub_C r₁).mul (Polynomial.monic_X_sub_C r₂)) hdvd (by
          rw [hd']
          rw [Polynomial.natDegree_mul
            (Polynomial.monic_X_sub_C r₁).ne_zero
            (Polynomial.monic_X_sub_C r₂).ne_zero]
          norm_num)
      by_cases hlt : r₁ < r₂
      · exact ⟨p.leadingCoeff, r₁, r₂, Polynomial.leadingCoeff_ne_zero.mpr hp0,
          hlt, heq.trans (mul_assoc _ _ _).symm⟩
      · have hlt' : r₂ < r₁ := lt_of_le_of_ne (le_of_not_gt hlt) hr.symm
        exact ⟨p.leadingCoeff, r₂, r₁, Polynomial.leadingCoeff_ne_zero.mpr hp0,
          hlt', heq.trans (by ring)⟩
    · rintro ⟨c, a, b, hc, hab, rfl⟩
      constructor
      · norm_num [hc]
      · exact ⟨a, b, ne_of_lt hab, by simp, by simp⟩
  constructor
  · intro hs
    have hc := hcand.mpr (hsol.mp hs)
    rcases hc with ⟨r, hord, hroot, hder⟩
    refine ⟨fun k => r (k + 1), ?_, ?_, ?_⟩
    · intro i
      apply hord (i + 1) (by simp; omega) (i + 2) (by simp; omega)
      omega
    · intro i
      exact hroot (i + 1) (by simp)
    · intro i
      simpa [Nat.add_assoc] using hder (i + 1) (by simp)
  · rintro ⟨r, hord, hroot, hder⟩
    apply hsol.mpr
    apply hcand.mp
    have hmono : StrictMonoOn r (Set.Iio n) := by
      apply strictMonoOn_of_lt_succ Set.ordConnected_Iio
      intro i _ hi his
      exact hord ⟨i, by simp at hi his ⊢; omega⟩
    refine ⟨fun k => r (k - 1), ?_, ?_, ?_⟩
    · intro i hi j hj hij
      apply hmono
      · simp at hi hj ⊢
        omega
      · simp at hi hj ⊢
        omega
      · simp at hi hj ⊢
        omega
    · intro i hi
      exact hroot ⟨i - 1, by simp at hi; omega⟩
    · intro i hi
      have hi1 : 1 ≤ i := by
        simp at hi
        omega
      dsimp
      simpa [Nat.sub_add_cancel hi1] using hder ⟨i - 1, by simp at hi; omega⟩
