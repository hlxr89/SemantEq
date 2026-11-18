import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_8_3_5a_assumed {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (n : ℕ) [Fact (1 < n)] [Fact (Nat.Prime n)] (h3 : n % 4 = 3) : Irreducible (2 : Polynomial (Zsqrtd (-n))) := by
  have hn2 : (2 : ℤ) < (n : ℤ) := by omega
  have hd : -(n : ℤ) ≤ 0 := by omega
  have unit_of_norm_one (z : Zsqrtd (-(n : ℤ))) (hz : z.norm = 1) : IsUnit z :=
    (Zsqrtd.norm_eq_one_iff' hd z).mp hz
  letI : NoZeroDivisors (Zsqrtd (-(n : ℤ))) := ⟨by
      intro a b h
      have hm := congrArg Zsqrtd.norm h
      rw [Zsqrtd.norm_mul] at hm
      simp only [Zsqrtd.norm_zero] at hm
      rcases mul_eq_zero.mp hm with ha | hb
      · left
        exact (Zsqrtd.norm_eq_zero_iff (by omega) a).mp ha
      · right
        exact (Zsqrtd.norm_eq_zero_iff (by omega) b).mp hb⟩
  have htwo : Irreducible (2 : Zsqrtd (-(n : ℤ))) := by
    rw [irreducible_iff]
    constructor
    · intro h
      have hh := (Zsqrtd.norm_eq_one_iff' hd (2 : Zsqrtd (-(n : ℤ)))).mpr h
      norm_num [Zsqrtd.norm_def] at hh
    · intro a b hab
      by_contra h
      rcases not_or.mp h with ⟨ha, hb⟩
      have ha1 : a.norm ≠ 1 := fun e => ha (unit_of_norm_one a e)
      have hb1 : b.norm ≠ 1 := fun e => hb (unit_of_norm_one b e)
      have ha0 := Zsqrtd.norm_nonneg hd a
      have hb0 := Zsqrtd.norm_nonneg hd b
      have hm := congrArg Zsqrtd.norm hab
      rw [Zsqrtd.norm_mul] at hm
      have hnormtwo : Zsqrtd.norm (2 : Zsqrtd (-(n : ℤ))) = 4 := by
        norm_num [Zsqrtd.norm_def]
      rw [hnormtwo] at hm
      have ha2 : 2 ≤ a.norm := by
        have : a.norm ≠ 0 := by intro e; rw [e] at hm; norm_num at hm
        omega
      have hb2 : 2 ≤ b.norm := by
        have : b.norm ≠ 0 := by intro e; rw [e] at hm; norm_num at hm
        omega
      have hae : a.norm = 2 := by nlinarith
      have he : a.re * a.re + (n : ℤ) * a.im * a.im = 2 := by
        simpa [Zsqrtd.norm_def] using hae
      have hai : a.im = 0 := by
        by_contra hi
        have hi' : 1 ≤ a.im ^ 2 := by
          have := sq_pos_of_ne_zero hi
          omega
        nlinarith [sq_nonneg a.re]
      rw [hai] at he
      norm_num at he
      have hlo : -2 < a.re := by nlinarith [sq_nonneg (a.re + 2)]
      have hhi : a.re < 2 := by nlinarith [sq_nonneg (a.re - 2)]
      interval_cases a.re <;> norm_num at he
  rw [irreducible_iff]
  constructor
  · change ¬IsUnit (Polynomial.C (2 : Zsqrtd (-(n : ℤ))))
    intro h
    exact htwo.not_isUnit (Polynomial.isUnit_C.mp h)
  · intro f g hfg
    have hc2 : (Polynomial.C (2 : Zsqrtd (-(n : ℤ)))) ≠ 0 := by norm_num
    have hf : f ≠ 0 := by
      intro e
      rw [e, zero_mul] at hfg
      exact hc2 hfg
    have hg : g ≠ 0 := by
      intro e
      rw [e, mul_zero] at hfg
      exact hc2 hfg
    have hdg := Polynomial.natDegree_mul hf hg
    rw [← hfg] at hdg
    simp at hdg
    have hdf : f.natDegree = 0 := by omega
    have hdg' : g.natDegree = 0 := by omega
    have ef := Polynomial.eq_C_of_natDegree_eq_zero hdf
    have eg := Polynomial.eq_C_of_natDegree_eq_zero hdg'
    have hc : (2 : Zsqrtd (-(n : ℤ))) = f.coeff 0 * g.coeff 0 := by
      rw [ef, eg] at hfg
      rw [← Polynomial.C_mul] at hfg
      exact Polynomial.C_injective hfg
    rcases htwo.isUnit_or_isUnit hc with hu | hu
    · left
      rw [ef, Polynomial.isUnit_C]
      exact hu
    · right
      rw [eg, Polynomial.isUnit_C]
      exact hu
