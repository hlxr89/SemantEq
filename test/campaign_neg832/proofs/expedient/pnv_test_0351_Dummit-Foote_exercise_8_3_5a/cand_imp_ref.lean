import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} (hn : n > 3 ∧ Nat.Prime n) : Irreducible (Polynomial.cyclotomic (2*(n+1)) ℤ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  have hd : -n < 0 := by omega
  have hd' : -n ≤ 0 := hd.le
  have norm_formula (z : Zsqrtd (-n)) : z.norm = z.re * z.re + n * z.im * z.im := by
    simp [Zsqrtd.norm_def]
  have norm_pos {z : Zsqrtd (-n)} (hz : z ≠ 0) : 0 < z.norm := by
    have := Zsqrtd.norm_nonneg hd' z
    exact lt_of_le_of_ne this (fun h => hz ((Zsqrtd.norm_eq_zero_iff hd z).mp h.symm))
  have unit_of_norm_one {z : Zsqrtd (-n)} (hz : z.norm = 1) : IsUnit z :=
    (Zsqrtd.norm_eq_one_iff' hd' z).mp hz
  constructor
  · refine ⟨?_, ?_⟩
    · intro h
      have hnorm := (Zsqrtd.norm_eq_one_iff' hd' (2 : Zsqrtd (-n))).mpr h
      norm_num [Zsqrtd.norm_def] at hnorm
    · intro x y hxy
      have hnorm : x.norm * y.norm = 4 := by
        rw [← Zsqrtd.norm_mul, ← hxy]
        norm_num [Zsqrtd.norm_def]
      by_cases hx : IsUnit x
      · exact Or.inl hx
      by_cases hy : IsUnit y
      · exact Or.inr hy
      exfalso
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        simp at hxy
      have hy0 : y ≠ 0 := by
        intro h
        subst y
        simp at hxy
      have hxp := norm_pos hx0
      have hyp := norm_pos hy0
      have hxn : x.norm ≠ 1 := fun h => hx (unit_of_norm_one h)
      have hyn : y.norm ≠ 1 := fun h => hy (unit_of_norm_one h)
      have hxge : 2 ≤ x.norm := by omega
      have hyge : 2 ≤ y.norm := by omega
      have hxeq : x.norm = 2 := by nlinarith
      rw [norm_formula] at hxeq
      have himsq : 1 ≤ x.im * x.im := by
        by_contra h
        have : x.im = 0 := by nlinarith [sq_nonneg x.im]
        rw [this] at hxeq
        norm_num at hxeq
        have hbad := Int.sq_ne_two_mod_four x.re
        rw [hxeq] at hbad
        norm_num at hbad
      nlinarith [sq_nonneg x.re]
  · constructor
    · refine ⟨?_, ?_⟩
      · intro h
        have hnorm := (Zsqrtd.norm_eq_one_iff' hd' (⟨0, 1⟩ : Zsqrtd (-n))).mpr h
        norm_num [Zsqrtd.norm_def] at hnorm
        omega
      · intro x y hxy
        have hnorm : x.norm * y.norm = n := by
          rw [← Zsqrtd.norm_mul, ← hxy]
          norm_num [Zsqrtd.norm_def]
        by_cases hxi : x.im = 0
        · have hdvd : x.re * x.re ∣ n := by
            use y.norm
            rw [norm_formula x, hxi] at hnorm
            norm_num at hnorm
            exact hnorm.symm
          have hu : IsUnit x.re := hn1 x.re hdvd
          left
          apply (Zsqrtd.isUnit_iff_norm_isUnit x).mpr
          rw [norm_formula, hxi]
          norm_num
          exact hu
        · right
          apply unit_of_norm_one
          have hxge : n ≤ x.norm := by
            rw [norm_formula]
            have hi : 1 ≤ x.im * x.im := by
              have := sq_pos_of_ne_zero hxi
              nlinarith
            nlinarith [sq_nonneg x.re]
          have hy0 : y ≠ 0 := by
            intro h
            subst y
            simp at hnorm
            omega
          have hyp := norm_pos hy0
          have : y.norm ≤ 1 := by nlinarith
          omega
    · refine ⟨?_, ?_⟩
      · intro h
        have hnorm := (Zsqrtd.norm_eq_one_iff' hd' (1 + ⟨0, 1⟩ : Zsqrtd (-n))).mpr h
        norm_num [Zsqrtd.norm_def] at hnorm
        omega
      · intro x y hxy
        have hre := congrArg Zsqrtd.re hxy
        have him := congrArg Zsqrtd.im hxy
        simp only [Zsqrtd.re_add, Zsqrtd.re_one, Zsqrtd.re_mul, Zsqrtd.im_add,
          Zsqrtd.im_one, Zsqrtd.im_mul] at hre him
        norm_num at hre him
        have hnorm : x.norm * y.norm = n + 1 := by
          rw [← Zsqrtd.norm_mul, ← hxy]
          norm_num [Zsqrtd.norm_def]
          ring
        by_cases hxi : x.im = 0
        · left
          apply (Zsqrtd.isUnit_iff_norm_isUnit x).mpr
          rw [norm_formula, hxi]
          norm_num
          have : x.re * y.im = 1 := by simpa [hxi] using him.symm
          exact isUnit_iff_exists_inv.mpr ⟨y.im, this⟩
        by_cases hyi : y.im = 0
        · right
          apply (Zsqrtd.isUnit_iff_norm_isUnit y).mpr
          rw [norm_formula, hyi]
          norm_num
          have : x.im * y.re = 1 := by simpa [hyi] using him.symm
          have hu : IsUnit y.re := isUnit_iff_exists_inv.mpr ⟨x.im, by simpa [mul_comm] using this⟩
          exact hu
        · exfalso
          have hxge : n ≤ x.norm := by
            rw [norm_formula]
            have hi : 1 ≤ x.im * x.im := by nlinarith [sq_pos_of_ne_zero hxi]
            nlinarith [sq_nonneg x.re]
          have hyge : n ≤ y.norm := by
            rw [norm_formula]
            have hi : 1 ≤ y.im * y.im := by nlinarith [sq_pos_of_ne_zero hyi]
            nlinarith [sq_nonneg y.re]
          have hprod : n * n ≤ x.norm * y.norm :=
            mul_le_mul hxge hyge (by omega) (by omega)
          nlinarith
