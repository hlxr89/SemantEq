import Mathlib

open Filter Topology
open Polynomial

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1991_a3_solution_ref : Set (Polynomial ℝ) := {p : Polynomial ℝ | p.degree = 2 ∧ (∃ r1 r2 : ℝ, r1 ≠ r2 ∧ p.eval r1 = 0 ∧ p.eval r2 = 0)}

def putnam_1991_a3_solution : Set (Polynomial ℝ) :=
  {p | ∃ c a b : ℝ, c ≠ 0 ∧ a < b ∧ p = C c * (X - C a) * (X - C b)}

-- ===== assumed statement (antecedent) =====
theorem putnam_1991_a3_refs_assumed
  (p : Polynomial ℝ)
  (n : ℕ)
  (hn : n = p.degree)
  (hge : n ≥ 2) :
  p ∈ putnam_1991_a3_solution_ref ↔
    (∃ r : ℕ → ℝ, (∀ i : Fin (n - 1), r i < r (i + 1)) ∧
    (∀ i : Fin n, p.eval (r i) = 0) ∧
    (∀ i : Fin (n - 1), (Polynomial.derivative p).eval ((r i + r (i + 1)) / 2) = 0)) :=
  by
    sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1991_a3 (n : ℕ) (hn : 2 ≤ n) (p : Polynomial ℝ) (hdeg : p.natDegree = n) :
    (∃ r : ℕ → ℝ,
      (∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i < j → r i < r j) ∧
      (∀ i ∈ Finset.Icc 1 n, p.eval (r i) = 0) ∧
      (∀ i ∈ Finset.Icc 1 (n - 1), (derivative p).eval ((r i + r (i + 1)) / 2) = 0)) ↔
    p ∈ putnam_1991_a3_solution := by
  have hp0 : p ≠ 0 := by
    intro hp
    simp [hp] at hdeg
    omega
  have hdegree : p.degree = (n : WithBot ℕ) := by
    rw [degree_eq_natDegree hp0, hdeg]
  have href := putnam_1991_a3_refs_assumed p n hdegree.symm hn
  have hsol : p ∈ putnam_1991_a3_solution_ref ↔ p ∈ putnam_1991_a3_solution := by
    constructor
    · rintro ⟨hpdeg, r₁, r₂, hne, hr₁, hr₂⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨p.leadingCoeff, r₁, r₂, leadingCoeff_ne_zero.mpr hp0, hlt, ?_⟩
        have hdvd₁ : X - C r₁ ∣ p := (dvd_iff_isRoot).2 hr₁
        have hdvd₂ : X - C r₂ ∣ p := (dvd_iff_isRoot).2 hr₂
        have hcop : IsCoprime (X - C r₁) (X - C r₂) :=
          isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne).isUnit
        have hdvd : (X - C r₁) * (X - C r₂) ∣ p := hcop.mul_dvd hdvd₁ hdvd₂
        simpa only [mul_assoc] using (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
          (monic_X_sub_C r₁ |>.mul (monic_X_sub_C r₂)) hdvd
          (by
            rw [(monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
            simpa using (natDegree_eq_of_degree_eq_some hpdeg).le))
      · refine ⟨p.leadingCoeff, r₂, r₁, leadingCoeff_ne_zero.mpr hp0, hgt, ?_⟩
        have hdvd₂ : X - C r₂ ∣ p := (dvd_iff_isRoot).2 hr₂
        have hdvd₁ : X - C r₁ ∣ p := (dvd_iff_isRoot).2 hr₁
        have hcop : IsCoprime (X - C r₂) (X - C r₁) :=
          isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne.symm).isUnit
        have hdvd : (X - C r₂) * (X - C r₁) ∣ p := hcop.mul_dvd hdvd₂ hdvd₁
        simpa only [mul_assoc] using (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
          (monic_X_sub_C r₂ |>.mul (monic_X_sub_C r₁)) hdvd
          (by
            rw [(monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
            simpa using (natDegree_eq_of_degree_eq_some hpdeg).le))
    · rintro ⟨c, a, b, hc, hab, rfl⟩
      constructor
      · norm_num [hc]
      · exact ⟨a, b, ne_of_lt hab, by simp, by simp⟩
  constructor
  · rintro ⟨r, horder, hroot, hderiv⟩
    apply hsol.mp
    apply href.mpr
    refine ⟨fun k => r (k + 1), ?_, ?_, ?_⟩
    · intro i
      exact horder (i + 1) (by simp; omega) (i + 2) (by simp; omega) (by omega)
    · intro i
      exact hroot (i + 1) (by simp)
    · intro i
      exact hderiv (i + 1) (by simp)
  · intro hsolp
    have hrefp := href.mp (hsol.mpr hsolp)
    rcases hrefp with ⟨s, hsorder, hsroot, hsderiv⟩
    refine ⟨fun k => s (k - 1), ?_, ?_, ?_⟩
    · intro i hi j hj hij
      simp only [Finset.mem_Icc] at hi hj
      have hmono : ∀ {u v : ℕ}, u < v → v < n → s u < s v := by
        intro u v huv hv
        induction v with
        | zero => omega
        | succ v ih =>
          by_cases huv' : u = v
          · subst u
            exact hsorder ⟨v, by omega⟩
          · exact lt_trans (ih (by omega) (by omega)) (hsorder ⟨v, by omega⟩)
      apply hmono (u := i - 1) (v := j - 1) <;> omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      exact hsroot ⟨i - 1, by omega⟩
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      have hibound : i - 1 < n - 1 := by omega
      have heq : i - 1 + 1 = i := by omega
      simpa [heq] using hsderiv ⟨i - 1, hibound⟩
