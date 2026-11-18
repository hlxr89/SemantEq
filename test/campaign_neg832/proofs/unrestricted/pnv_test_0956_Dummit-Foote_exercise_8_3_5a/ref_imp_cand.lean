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
  have hn3 : 3 ≤ n := by omega
  have hneg : -(n : ℤ) < 0 := by omega
  have hnonpos : -(n : ℤ) ≤ 0 := hneg.le
  have norm_pos_of_nonzero (z : Zsqrtd (-(n : ℤ))) (hz : z ≠ 0) : 0 < z.norm := by
    have hz0 : z.norm ≠ 0 := by
      intro h
      exact hz ((Zsqrtd.norm_eq_zero_iff hneg z).mp h)
    exact lt_of_le_of_ne (Zsqrtd.norm_nonneg hnonpos z) (Ne.symm hz0)
  have norm_ge_two_of_not_unit (z : Zsqrtd (-(n : ℤ))) (hz : z ≠ 0)
      (hu : ¬IsUnit z) : 2 ≤ z.norm := by
    have hp := norm_pos_of_nonzero z hz
    have hn1 : z.norm ≠ 1 := by
      intro h
      exact hu ((Zsqrtd.norm_eq_one_iff' hnonpos z).mp h)
    omega
  have hirr : Irreducible (2 : Zsqrtd (-(n : ℤ))) := by
    rw [irreducible_iff]
    constructor
    · intro hu
      have hnorm : Zsqrtd.norm (2 : Zsqrtd (-(n : ℤ))) = 1 :=
        (Zsqrtd.norm_eq_one_iff' hnonpos _).mpr hu
      norm_num [Zsqrtd.norm] at hnorm
    · intro a b hab
      by_contra h
      push_neg at h
      have ha0 : a ≠ 0 := by
        intro ha
        subst a
        norm_num at hab
      have hb0 : b ≠ 0 := by
        intro hb
        subst b
        norm_num at hab
      have ha2 := norm_ge_two_of_not_unit a ha0 h.1
      have hb2 := norm_ge_two_of_not_unit b hb0 h.2
      have hnorm := congr_arg Zsqrtd.norm hab
      simp only [Zsqrtd.norm_mul] at hnorm
      have htwo : Zsqrtd.norm (2 : Zsqrtd (-(n : ℤ))) = 4 := by
        norm_num [Zsqrtd.norm]
      rw [htwo] at hnorm
      have hmulnonneg : 0 ≤ a.norm * (b.norm - 2) :=
        mul_nonneg (Zsqrtd.norm_nonneg hnonpos a) (sub_nonneg.mpr hb2)
      have hna : a.norm = 2 := by nlinarith
      rw [Zsqrtd.norm_def] at hna
      have him : a.im = 0 := by
        by_contra hi
        have hi1 : 1 ≤ a.im * a.im := by
          rcases lt_or_gt_of_ne hi with hi | hi <;> nlinarith
        norm_num at hna
        nlinarith [sq_nonneg a.re]
      simp [him] at hna
      have hlo : -2 < a.re := by nlinarith [sq_nonneg (a.re + 2)]
      have hhi : a.re < 2 := by nlinarith [sq_nonneg (a.re - 2)]
      interval_cases a.re <;> norm_num at hna
  letI : NoZeroDivisors (Zsqrtd (-(n : ℤ))) :=
    { eq_zero_or_eq_zero_of_mul_eq_zero := by
        intro a b hab
        have hnorm := congr_arg Zsqrtd.norm hab
        rw [Zsqrtd.norm_mul, Zsqrtd.norm_zero] at hnorm
        rcases mul_eq_zero.mp hnorm with ha | hb
        · exact Or.inl ((Zsqrtd.norm_eq_zero_iff hneg a).mp ha)
        · exact Or.inr ((Zsqrtd.norm_eq_zero_iff hneg b).mp hb) }
  have constant_irreducible {R : Type} [CommRing R] [NoZeroDivisors R] {r : R}
      (hr : Irreducible r) : Irreducible (Polynomial.C r) := by
    have hr0 : r ≠ 0 := hr.ne_zero
    rw [irreducible_iff] at hr ⊢
    constructor
    · exact fun hu => hr.1 (Polynomial.isUnit_C.mp hu)
    · intro f g hfg
      have hf0 : f ≠ 0 := by
        intro hf
        subst f
        simp at hfg
        exact hr0 hfg
      have hg0 : g ≠ 0 := by
        intro hg
        subst g
        simp at hfg
        exact hr0 hfg
      have hdeg : f.natDegree + g.natDegree = 0 := by
        rw [← Polynomial.natDegree_mul hf0 hg0, ← hfg]
        simp
      have hfdeg : f.natDegree = 0 := (Nat.add_eq_zero_iff.mp hdeg).1
      have hgdeg : g.natDegree = 0 := (Nat.add_eq_zero_iff.mp hdeg).2
      rw [Polynomial.eq_C_of_natDegree_eq_zero hfdeg,
        Polynomial.eq_C_of_natDegree_eq_zero hgdeg] at hfg ⊢
      simp only [← Polynomial.C_mul, Polynomial.C_inj] at hfg
      rcases hr.2 hfg with hf | hg
      · exact Or.inl (Polynomial.isUnit_C.mpr hf)
      · exact Or.inr (Polynomial.isUnit_C.mpr hg)
  change Irreducible (Polynomial.C (2 : Zsqrtd (-(n : ℤ))))
  exact constant_irreducible hirr
