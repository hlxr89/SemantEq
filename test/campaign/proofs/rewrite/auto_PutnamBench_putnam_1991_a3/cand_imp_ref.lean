import Mathlib

open Filter Topology
open Polynomial

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1991_a3_solution_ref : Set (Polynomial ℝ) := {p : Polynomial ℝ | p.degree = 2 ∧ (∃ r1 r2 : ℝ, r1 ≠ r2 ∧ p.eval r1 = 0 ∧ p.eval r2 = 0)}

def putnam_1991_a3_solution : Set (Polynomial ℝ) :=
  {p | ∃ c a b : ℝ, c ≠ 0 ∧ a < b ∧ p = C c * (X - C a) * (X - C b)}

-- ===== assumed statement (antecedent) =====
theorem putnam_1991_a3_assumed (n : ℕ) (hn : 2 ≤ n) (p : Polynomial ℝ) (hdeg : p.natDegree = n) :
    (∃ r : ℕ → ℝ,
      (∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i < j → r i < r j) ∧
      (∀ i ∈ Finset.Icc 1 n, p.eval (r i) = 0) ∧
      (∀ i ∈ Finset.Icc 1 (n - 1), (derivative p).eval ((r i + r (i + 1)) / 2) = 0)) ↔
    p ∈ putnam_1991_a3_solution := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1991_a3_refs
  (p : Polynomial ℝ)
  (n : ℕ)
  (hn : n = p.degree)
  (hge : n ≥ 2) :
  p ∈ putnam_1991_a3_solution_ref ↔
    (∃ r : ℕ → ℝ, (∀ i : Fin (n - 1), r i < r (i + 1)) ∧
    (∀ i : Fin n, p.eval (r i) = 0) ∧
    (∀ i : Fin (n - 1), (Polynomial.derivative p).eval ((r i + r (i + 1)) / 2) = 0)) := by
  have hp0 : p ≠ 0 := by
    intro hp
    subst p
    exact WithBot.coe_ne_bot (hn.trans degree_zero)
  have hnatdegree : p.natDegree = n := by
    apply WithBot.coe_eq_coe.mp
    exact (degree_eq_natDegree hp0).symm.trans hn.symm
  have hsolution : p ∈ putnam_1991_a3_solution_ref ↔ p ∈ putnam_1991_a3_solution := by
    constructor
    · rintro ⟨hpdeg, a, b, hab, ha, hb⟩
      have hle : (X - C a) * (X - C b) ∣ p := by
        apply (isCoprime_X_sub_C_of_isUnit_sub ((sub_ne_zero.mpr hab).isUnit)).mul_dvd
        · exact dvd_iff_isRoot.mpr ha
        · exact dvd_iff_isRoot.mpr hb
      have hpndeg : p.natDegree = 2 := by
        apply WithBot.coe_eq_coe.mp
        exact (degree_eq_natDegree hp0).symm.trans hpdeg
      have heq := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
        ((monic_X_sub_C a).mul (monic_X_sub_C b)) hle
        (by rw [hpndeg, natDegree_mul (X_sub_C_ne_zero a) (X_sub_C_ne_zero b),
          natDegree_X_sub_C, natDegree_X_sub_C])
      refine ⟨p.leadingCoeff, min a b, max a b, leadingCoeff_ne_zero.mpr hp0,
        min_lt_max.mpr hab, ?_⟩
      · rcases le_total a b with hab' | hba'
        · rw [min_eq_left hab', max_eq_right hab']
          simpa only [← mul_assoc] using heq
        · have hba : b ≤ a := hba'
          rw [min_eq_right hba, max_eq_left hba]
          simpa only [mul_assoc, mul_comm (X - C a) (X - C b)] using heq
    · rintro ⟨c, a, b, hc, hab, rfl⟩
      constructor
      · simp only [degree_mul, degree_C hc, degree_X_sub_C, zero_add]
        rfl
      · refine ⟨a, b, ne_of_lt hab, ?_, ?_⟩
        · simp only [eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero, zero_mul]
        · simp only [eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]
  constructor
  · intro hsol
    obtain ⟨r, hrord, hrroot, hrderiv⟩ :=
      (putnam_1991_a3_assumed n hge p hnatdegree).mpr (hsolution.mp hsol)
    refine ⟨fun k => r (k + 1), ?_, ?_, ?_⟩
    · intro i
      apply hrord (i + 1) (Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 i, ?_⟩)
        (i + 2) (Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 (i + 1), ?_⟩)
        (Nat.lt_succ_self (i + 1))
      · exact le_trans (Nat.succ_le_of_lt i.isLt) (Nat.sub_le n 1)
      · exact (Nat.succ_le_succ (Nat.succ_le_of_lt i.isLt)).trans_eq
          (Nat.sub_add_cancel (le_trans (Nat.succ_le_succ (Nat.zero_le 1)) hge))
    · intro i
      exact hrroot (i + 1) (Finset.mem_Icc.mpr
        ⟨Nat.le_add_left 1 i, Nat.succ_le_of_lt i.isLt⟩)
    · intro i
      exact hrderiv (i + 1) (Finset.mem_Icc.mpr
        ⟨Nat.le_add_left 1 i, Nat.succ_le_of_lt i.isLt⟩)
  · rintro ⟨r, hrord, hrroot, hrderiv⟩
    apply hsolution.mpr
    apply (putnam_1991_a3_assumed n hge p hnatdegree).mp
    have hf : StrictMonoOn r (Set.Iic (n - 1)) :=
      strictMonoOn_Iic_of_lt_succ fun k hk => hrord ⟨k, hk⟩
    refine ⟨fun i => r (i - 1), ?_, ?_, ?_⟩
    · intro i hi j hj hij
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      apply hf (Nat.sub_le_sub_right (Finset.mem_Icc.mp hi).2 1)
        (Nat.sub_le_sub_right (Finset.mem_Icc.mp hj).2 1)
      apply (Nat.add_lt_add_iff_right (k := 1)).mp
      simpa only [Nat.sub_add_cancel hi1, Nat.sub_add_cancel hj1] using hij
    · intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hin : i - 1 < n := lt_of_lt_of_le
        (Nat.sub_lt (Nat.zero_lt_of_lt hi1) Nat.zero_lt_one) (Finset.mem_Icc.mp hi).2
      exact hrroot ⟨i - 1, hin⟩
    · intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hin : i - 1 < n - 1 := lt_of_lt_of_le
        (Nat.sub_lt (Nat.zero_lt_of_lt hi1) Nat.zero_lt_one) (Finset.mem_Icc.mp hi).2
      simpa only [Nat.sub_add_cancel hi1] using hrderiv ⟨i - 1, hin⟩
