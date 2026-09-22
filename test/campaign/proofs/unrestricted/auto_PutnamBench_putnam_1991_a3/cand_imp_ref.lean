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
  have hdegree : p.degree = (n : WithBot ℕ) := by simpa using hn.symm
  have hnat : p.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hdegree
  have hcand := putnam_1991_a3_assumed n hge p hnat

  have hsolutions : p ∈ putnam_1991_a3_solution ↔ p ∈ putnam_1991_a3_solution_cand := by
    constructor
    · rintro ⟨hdegree2, a, b, hab, ha, hb⟩
      have hnat2 : p.natDegree = 2 := Polynomial.natDegree_eq_of_degree_eq_some hdegree2
      have hda : X - C a ∣ p := Polynomial.dvd_iff_isRoot.mpr ha
      have hdb : X - C b ∣ p := Polynomial.dvd_iff_isRoot.mpr hb
      have hcop : IsCoprime (X - C a) (X - C b) :=
        Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
      have hdvd : (X - C a) * (X - C b) ∣ p := hcop.mul_dvd hda hdb
      have heq : p = C p.leadingCoeff * ((X - C a) * (X - C b)) :=
        Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
          ((Polynomial.monic_X_sub_C a).mul (Polynomial.monic_X_sub_C b)) hdvd (by
            rw [hnat2]
            rw [(Polynomial.monic_X_sub_C a).natDegree_mul (Polynomial.monic_X_sub_C b)]
            simp)
      have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
      rcases lt_or_gt_of_ne hab with hab' | hba'
      · refine ⟨p.leadingCoeff, a, b, hlc, hab', ?_⟩
        exact heq.trans (mul_assoc _ _ _).symm
      · refine ⟨p.leadingCoeff, b, a, hlc, hba', ?_⟩
        calc
          p = C p.leadingCoeff * ((X - C a) * (X - C b)) := heq
          _ = C p.leadingCoeff * ((X - C b) * (X - C a)) := by rw [mul_comm (X - C a)]
          _ = C p.leadingCoeff * (X - C b) * (X - C a) := (mul_assoc _ _ _).symm
    · rintro ⟨c, a, b, hc, hab, rfl⟩
      constructor
      · apply (Polynomial.degree_eq_iff_natDegree_eq
          (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hc) (X_sub_C_ne_zero a))
            (X_sub_C_ne_zero b))).2
        rw [Polynomial.natDegree_mul
          (mul_ne_zero (C_ne_zero.mpr hc) (X_sub_C_ne_zero a)) (X_sub_C_ne_zero b),
          Polynomial.natDegree_C_mul hc]
        simp
      · exact ⟨a, b, ne_of_lt hab, by simp, by simp⟩

  have hconditions :
      (∃ r : ℕ → ℝ,
        (∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i < j → r i < r j) ∧
        (∀ i ∈ Finset.Icc 1 n, p.eval (r i) = 0) ∧
        (∀ i ∈ Finset.Icc 1 (n - 1), (derivative p).eval ((r i + r (i + 1)) / 2) = 0)) ↔
      (∃ r : ℕ → ℝ, (∀ i : Fin (n - 1), r i < r (i + 1)) ∧
        (∀ i : Fin n, p.eval (r i) = 0) ∧
        (∀ i : Fin (n - 1), (Polynomial.derivative p).eval ((r i + r (i + 1)) / 2) = 0)) := by
    constructor
    · rintro ⟨r, hmono, hroots, hderiv⟩
      refine ⟨fun k => r (k + 1), ?_, ?_, ?_⟩
      · intro i
        apply hmono (i + 1) (by simp [Finset.mem_Icc]; omega) (i + 2) (by simp [Finset.mem_Icc]; omega)
        omega
      · intro i
        apply hroots (i + 1)
        simp [Finset.mem_Icc]
      · intro i
        apply hderiv (i + 1)
        simp [Finset.mem_Icc]
    · rintro ⟨r, hadj, hroots, hderiv⟩
      have hmono : StrictMono (fun i : Fin n => r i) := by
        rw [show n = (n - 1) + 1 by omega]
        apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        simpa using hadj i
      let s : ℕ → ℝ := fun k => r (k - 1)
      refine ⟨s, ?_, ?_, ?_⟩
      · intro i hi j hj hij
        simp only [s]
        rcases Finset.mem_Icc.mp hi with ⟨hi1, hin⟩
        rcases Finset.mem_Icc.mp hj with ⟨hj1, hjn⟩
        have hlt : (⟨i - 1, by omega⟩ : Fin n) < ⟨j - 1, by omega⟩ := by
          simp only [Fin.mk_lt_mk]
          omega
        exact hmono hlt
      · intro i hi
        simp only [s]
        rcases Finset.mem_Icc.mp hi with ⟨hi1, hin⟩
        exact hroots ⟨i - 1, by omega⟩
      · intro i hi
        simp only [s]
        rcases Finset.mem_Icc.mp hi with ⟨hi1, hin⟩
        have hik : i - 1 < n - 1 := by omega
        simpa [Nat.sub_add_cancel hi1] using hderiv ⟨i - 1, hik⟩

  calc
    _ ↔ p ∈ putnam_1991_a3_solution_cand := hsolutions
    _ ↔ _ := hcand.symm
    _ ↔ _ := hconditions
