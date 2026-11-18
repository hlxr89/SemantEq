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
    simp only [Zsqrtd.norm_def]
    ring
  have norm_pos (z : Zsqrtd (-n)) (hz : z ≠ 0) : 0 < z.norm := by
    have hnonneg := Zsqrtd.norm_nonneg hd' z
    have hne : z.norm ≠ 0 := fun h => hz ((Zsqrtd.norm_eq_zero_iff hd z).mp h)
    omega
  have unit_of_norm_one (z : Zsqrtd (-n)) (hz : z.norm = 1) : IsUnit z :=
    (Zsqrtd.norm_eq_one_iff' hd' z).mp hz
  have norm_ge_n_of_im_ne_zero (z : Zsqrtd (-n)) (hz : z.im ≠ 0) : n ≤ z.norm := by
    rw [norm_formula]
    have him : 1 ≤ z.im * z.im := by
      simpa [pow_two] using (one_le_sq_iff_one_le_abs z.im).2 (Int.one_le_abs hz)
    have hre : 0 ≤ z.re * z.re := mul_self_nonneg z.re
    nlinarith
  have norm_ne_two (z : Zsqrtd (-n)) : z.norm ≠ 2 := by
    intro hz
    rw [norm_formula] at hz
    have hre : 0 ≤ z.re * z.re := mul_self_nonneg z.re
    have him : 0 ≤ z.im * z.im := mul_self_nonneg z.im
    have him0 : z.im = 0 := by
      by_contra hne
      have him1 : 1 ≤ z.im * z.im := by
        simpa [pow_two] using (one_le_sq_iff_one_le_abs z.im).2 (Int.one_le_abs hne)
      nlinarith
    simp [him0] at hz
    have hlo : -2 < z.re := by nlinarith
    have hhi : z.re < 2 := by nlinarith
    interval_cases z.re <;> norm_num at hz
  have factor_units
      (x y t : Zsqrtd (-n)) (ht : t = x * y) (ht0 : t ≠ 0)
      (hlarge : x.im ≠ 0 ∨ y.im ≠ 0)
      (htnorm : t.norm ≤ n + 1) : IsUnit x ∨ IsUnit y := by
    have hxy0 : x * y ≠ 0 := by simpa [← ht] using ht0
    have hx0 : x ≠ 0 := fun h => hxy0 (by simp [h])
    have hy0 : y ≠ 0 := fun h => hxy0 (by simp [h])
    have hxpos := norm_pos x hx0
    have hypos := norm_pos y hy0
    have hnorm : t.norm = x.norm * y.norm := by rw [ht, Zsqrtd.norm_mul]
    rcases hlarge with hxim | hyim
    · have hxlarge := norm_ge_n_of_im_ne_zero x hxim
      by_cases hy1 : y.norm = 1
      · exact Or.inr (unit_of_norm_one y hy1)
      · have hy2 : 2 ≤ y.norm := by omega
        nlinarith
    · have hylarge := norm_ge_n_of_im_ne_zero y hyim
      by_cases hx1 : x.norm = 1
      · exact Or.inl (unit_of_norm_one x hx1)
      · have hx2 : 2 ≤ x.norm := by omega
        nlinarith
  constructor
  · rw [irreducible_iff]
    constructor
    · intro hu
      have hnorm := (Zsqrtd.norm_eq_one_iff' hd' (2 : Zsqrtd (-n))).mpr hu
      norm_num [Zsqrtd.norm_def] at hnorm
    · intro x y hxy
      have ht0 : (2 : Zsqrtd (-n)) ≠ 0 := by norm_num
      have hprod : x.norm * y.norm = 4 := by
        calc
          x.norm * y.norm = (x * y).norm := (Zsqrtd.norm_mul x y).symm
          _ = (2 : Zsqrtd (-n)).norm := congrArg Zsqrtd.norm hxy.symm
          _ = 4 := by norm_num [Zsqrtd.norm_def]
      have hxy0 : x * y ≠ 0 := by simpa [← hxy] using ht0
      have hx0 : x ≠ 0 := fun h => hxy0 (by simp [h])
      have hy0 : y ≠ 0 := fun h => hxy0 (by simp [h])
      have hxpos := norm_pos x hx0
      have hypos := norm_pos y hy0
      by_cases hx1 : x.norm = 1
      · exact Or.inl (unit_of_norm_one x hx1)
      by_cases hy1 : y.norm = 1
      · exact Or.inr (unit_of_norm_one y hy1)
      have hx2 : x.norm = 2 := by
        have : 2 ≤ x.norm := by omega
        have : 2 ≤ y.norm := by omega
        nlinarith
      exact (norm_ne_two x hx2).elim
  constructor
  · rw [irreducible_iff]
    constructor
    · intro hu
      have hnorm := (Zsqrtd.norm_eq_one_iff' hd' (⟨0, 1⟩ : Zsqrtd (-n))).mpr hu
      simp [Zsqrtd.norm_def] at hnorm
      omega
    · intro x y hxy
      apply factor_units x y (⟨0, 1⟩ : Zsqrtd (-n)) hxy
      · intro h
        have := congr_arg Zsqrtd.im h
        norm_num at this
      · have him := congr_arg Zsqrtd.im hxy
        simp only [Zsqrtd.im_mul] at him
        by_contra h
        push_neg at h
        rcases h with ⟨hx, hy⟩
        simp [hx, hy] at him
      · simp [Zsqrtd.norm_def]
  · rw [irreducible_iff]
    constructor
    · intro hu
      have hnorm := (Zsqrtd.norm_eq_one_iff' hd' (1 + ⟨0, 1⟩ : Zsqrtd (-n))).mpr hu
      simp [Zsqrtd.norm_def] at hnorm
      omega
    · intro x y hxy
      apply factor_units x y (1 + ⟨0, 1⟩ : Zsqrtd (-n)) hxy
      · intro h
        have := congr_arg Zsqrtd.re h
        norm_num at this
      · have him := congr_arg Zsqrtd.im hxy
        simp only [Zsqrtd.im_add, Zsqrtd.im_one, Zsqrtd.im_mul] at him
        by_contra h
        push_neg at h
        rcases h with ⟨hx, hy⟩
        simp [hx, hy] at him
      · simp [Zsqrtd.norm_def]
        omega
