import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) [Fact (1 < n)] [Fact (Nat.Prime n)] (h3 : n % 4 = 3) : Irreducible (2 : Polynomial (Zsqrtd (-n))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  have hneg : -n < 0 := by omega
  have hnonpos : -n ≤ 0 := hneg.le
  have norm_pos_of_nonzero (z : Zsqrtd (-n)) (hz : z ≠ 0) : 0 < z.norm := by
    have hz0 : z.norm ≠ 0 := by
      intro h
      exact hz ((Zsqrtd.norm_eq_zero_iff hneg z).mp h)
    exact lt_of_le_of_ne (Zsqrtd.norm_nonneg hnonpos z) (Ne.symm hz0)
  have norm_ge_two_of_not_unit (z : Zsqrtd (-n)) (hz : z ≠ 0) (hu : ¬IsUnit z) :
      2 ≤ z.norm := by
    have hp := norm_pos_of_nonzero z hz
    have hn1 : z.norm ≠ 1 := by
      intro h
      exact hu ((Zsqrtd.norm_eq_one_iff' hnonpos z).mp h)
    omega
  have irreducible_two : Irreducible (2 : Zsqrtd (-n)) := by
    rw [irreducible_iff]
    constructor
    · intro hu
      have hnorm : Zsqrtd.norm (2 : Zsqrtd (-n)) = 1 :=
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
      have htwo : Zsqrtd.norm (2 : Zsqrtd (-n)) = 4 := by
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
        nlinarith [sq_nonneg a.re]
      simp [him] at hna
      have hlo : -2 < a.re := by nlinarith [sq_nonneg (a.re + 2)]
      have hhi : a.re < 2 := by nlinarith [sq_nonneg (a.re - 2)]
      interval_cases a.re <;> norm_num at hna
  have irreducible_im_one (x : Zsqrtd (-n)) (hxim : x.im = 1)
      (hxnorm : x.norm ≤ n + 1) : Irreducible x := by
    rw [irreducible_iff]
    constructor
    · intro hu
      have hone : x.norm = 1 := (Zsqrtd.norm_eq_one_iff' hnonpos _).mpr hu
      rw [Zsqrtd.norm_def, hxim] at hone
      nlinarith [sq_nonneg x.re]
    · intro a b hab
      by_contra h
      push_neg at h
      have hx0 : x ≠ 0 := by
        intro hx
        have := congr_arg Zsqrtd.im hx
        simp [hxim] at this
      have ha0 : a ≠ 0 := by
        intro ha
        apply hx0
        rw [hab, ha, zero_mul]
      have hb0 : b ≠ 0 := by
        intro hb
        apply hx0
        rw [hab, hb, mul_zero]
      have ha2 := norm_ge_two_of_not_unit a ha0 h.1
      have hb2 := norm_ge_two_of_not_unit b hb0 h.2
      have hnorm := congr_arg Zsqrtd.norm hab
      simp only [Zsqrtd.norm_mul] at hnorm
      rw [hnorm] at hxnorm
      have hmulnonneg : 0 ≤ a.norm * (b.norm - 2) :=
        mul_nonneg (Zsqrtd.norm_nonneg hnonpos a) (sub_nonneg.mpr hb2)
      have hna_lt : a.norm < n := by
        nlinarith
      have haim : a.im = 0 := by
        by_contra hi
        have hi1 : 1 ≤ a.im * a.im := by
          rcases lt_or_gt_of_ne hi with hi | hi <;> nlinarith
        rw [Zsqrtd.norm_def] at hna_lt
        nlinarith [sq_nonneg a.re]
      have himmul := congr_arg Zsqrtd.im hab
      simp only [Zsqrtd.im_mul, hxim, haim, zero_mul, add_zero] at himmul
      have hare : a.re = 1 ∨ a.re = -1 :=
        Int.eq_one_or_neg_one_of_mul_eq_one himmul.symm
      have haunit : IsUnit a := by
        rw [← Zsqrtd.norm_eq_one_iff' hnonpos]
        rw [Zsqrtd.norm_def, haim]
        rcases hare with hare | hare <;> simp [hare]
      exact h.1 haunit
  refine ⟨irreducible_two, ?_, ?_⟩
  · apply irreducible_im_one (⟨0, 1⟩ : Zsqrtd (-n)) rfl
    simp [Zsqrtd.norm, add_comm]
  · apply irreducible_im_one (1 + ⟨0, 1⟩ : Zsqrtd (-n)) (by rfl)
    simp [Zsqrtd.norm, add_comm]
