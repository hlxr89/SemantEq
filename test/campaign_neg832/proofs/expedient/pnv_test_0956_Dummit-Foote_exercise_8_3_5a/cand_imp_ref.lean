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
  have hd : -n ≤ 0 := by omega
  have unit_of_norm_one (z : Zsqrtd (-n)) (hz : z.norm = 1) : IsUnit z :=
    (Zsqrtd.norm_eq_one_iff' hd z).mp hz
  constructor
  · rw [irreducible_iff]
    constructor
    · intro h
      have hh := (Zsqrtd.norm_eq_one_iff' hd (2 : Zsqrtd (-n))).mpr h
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
      have htwo : Zsqrtd.norm (2 : Zsqrtd (-n)) = 4 := by
        norm_num [Zsqrtd.norm_def]
      rw [htwo] at hm
      have ha2 : 2 ≤ a.norm := by
        have : a.norm ≠ 0 := by intro e; rw [e] at hm; norm_num at hm
        omega
      have hb2 : 2 ≤ b.norm := by
        have : b.norm ≠ 0 := by intro e; rw [e] at hm; norm_num at hm
        omega
      have hae : a.norm = 2 := by nlinarith
      have he : a.re * a.re + n * a.im * a.im = 2 := by
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
  · constructor
    · rw [irreducible_iff]
      constructor
      · intro h
        have hh := (Zsqrtd.norm_eq_one_iff' hd (⟨0, 1⟩ : Zsqrtd (-n))).mpr h
        norm_num [Zsqrtd.norm_def] at hh
        omega
      · intro a b hab
        by_contra h
        rcases not_or.mp h with ⟨ha, hb⟩
        have ha1 : a.norm ≠ 1 := fun e => ha (unit_of_norm_one a e)
        have hb1 : b.norm ≠ 1 := fun e => hb (unit_of_norm_one b e)
        have ha0 := Zsqrtd.norm_nonneg hd a
        have hb0 := Zsqrtd.norm_nonneg hd b
        have hm := congrArg Zsqrtd.norm hab
        rw [Zsqrtd.norm_mul] at hm
        have hsqrt : Zsqrtd.norm (⟨0, 1⟩ : Zsqrtd (-n)) = n := by
          simp [Zsqrtd.norm_def]
        rw [hsqrt] at hm
        have ha2 : 2 ≤ a.norm := by
          have : a.norm ≠ 0 := by intro e; rw [e] at hm; omega
          omega
        have hb2 : 2 ≤ b.norm := by
          have : b.norm ≠ 0 := by intro e; rw [e] at hm; omega
          omega
        have hale : a.norm ≤ n := by nlinarith
        have hae : a.re * a.re + n * a.im * a.im = a.norm := by
          simp [Zsqrtd.norm_def]
        have hai2 : a.im ^ 2 ≤ 1 := by
          rw [pow_two]
          nlinarith [sq_nonneg a.re]
        have hailo : -2 < a.im := by nlinarith [sq_nonneg (a.im + 2)]
        have haihi : a.im < 2 := by nlinarith [sq_nonneg (a.im - 2)]
        interval_cases hi : a.im
        · have hare : a.re = 0 := by
            norm_num at hae
            nlinarith [sq_nonneg a.re]
          have haeq : a.norm = n := by simp [Zsqrtd.norm_def, hi, hare]
          rw [haeq] at hm
          have : b.norm = 1 := by nlinarith
          exact hb (unit_of_norm_one b this)
        · have hdiv : a.re * a.re ∣ n := by
            use b.norm
            calc
              n = a.norm * b.norm := hm
              _ = (a.re * a.re) * b.norm := by rw [← hae]; norm_num
          have hru := hn1 a.re hdiv
          rcases Int.isUnit_iff.mp hru with hr | hr
          · have : a.norm = 1 := by simp [Zsqrtd.norm_def, hi, hr]
            exact ha (unit_of_norm_one a this)
          · have : a.norm = 1 := by simp [Zsqrtd.norm_def, hi, hr]
            exact ha (unit_of_norm_one a this)
        · have hare : a.re = 0 := by
            norm_num at hae
            nlinarith [sq_nonneg a.re]
          have haeq : a.norm = n := by simp [Zsqrtd.norm_def, hi, hare]
          rw [haeq] at hm
          have : b.norm = 1 := by nlinarith
          exact hb (unit_of_norm_one b this)
    · rw [irreducible_iff]
      constructor
      · intro h
        have hh := (Zsqrtd.norm_eq_one_iff' hd (1 + ⟨0, 1⟩ : Zsqrtd (-n))).mpr h
        norm_num [Zsqrtd.norm_def] at hh
        omega
      · intro a b hab
        by_contra h
        rcases not_or.mp h with ⟨ha, hb⟩
        have ha1 : a.norm ≠ 1 := fun e => ha (unit_of_norm_one a e)
        have hb1 : b.norm ≠ 1 := fun e => hb (unit_of_norm_one b e)
        have ha0 := Zsqrtd.norm_nonneg hd a
        have hb0 := Zsqrtd.norm_nonneg hd b
        have hm := congrArg Zsqrtd.norm hab
        rw [Zsqrtd.norm_mul] at hm
        have ht : Zsqrtd.norm (1 + ⟨0, 1⟩ : Zsqrtd (-n)) = n + 1 := by
          simp [Zsqrtd.norm_def]
          ring
        rw [ht] at hm
        have ha2 : 2 ≤ a.norm := by
          have : a.norm ≠ 0 := by intro e; rw [e] at hm; omega
          omega
        have hb2 : 2 ≤ b.norm := by
          have : b.norm ≠ 0 := by intro e; rw [e] at hm; omega
          omega
        have hale : a.norm ≤ n + 1 := by nlinarith
        have hae : a.re * a.re + n * a.im * a.im = a.norm := by
          simp [Zsqrtd.norm_def]
        have hai2lt : a.im ^ 2 < 2 := by
          rw [pow_two]
          nlinarith [sq_nonneg a.re]
        have hailo : -2 < a.im := by nlinarith [sq_nonneg (a.im + 2)]
        have haihi : a.im < 2 := by nlinarith [sq_nonneg (a.im - 2)]
        interval_cases hi : a.im
        · have hare2 : a.re ^ 2 ≤ 1 := by
            norm_num at hae
            rw [pow_two]
            nlinarith
          have hrelo : -2 < a.re := by nlinarith [sq_nonneg (a.re + 2)]
          have hrehi : a.re < 2 := by nlinarith [sq_nonneg (a.re - 2)]
          interval_cases hr : a.re
          · have haeq : a.norm = n + 1 := by simp [Zsqrtd.norm_def, hi, hr]; ring
            rw [haeq] at hm
            have hc : (n + 1) * 1 = (n + 1) * b.norm := by simpa using hm
            have : b.norm = 1 := (mul_left_cancel₀ (by omega : n + 1 ≠ 0) hc).symm
            exact hb (unit_of_norm_one b this)
          · have haeq : a.norm = n := by simp [Zsqrtd.norm_def, hi, hr]
            rw [haeq] at hm
            have hnb : n * 2 ≤ n * b.norm :=
              mul_le_mul_of_nonneg_left hb2 (by omega)
            omega
          · have haeq : a.norm = n + 1 := by simp [Zsqrtd.norm_def, hi, hr]; ring
            rw [haeq] at hm
            have hc : (n + 1) * 1 = (n + 1) * b.norm := by simpa using hm
            have : b.norm = 1 := (mul_left_cancel₀ (by omega : n + 1 ≠ 0) hc).symm
            exact hb (unit_of_norm_one b this)
        · have him := congrArg Zsqrtd.im hab
          simp [hi] at him
          have hru : IsUnit a.re := isUnit_iff_exists_inv.mpr ⟨b.im, him.symm⟩
          rcases Int.isUnit_iff.mp hru with hr | hr
          · have : a.norm = 1 := by simp [Zsqrtd.norm_def, hi, hr]
            exact ha (unit_of_norm_one a this)
          · have : a.norm = 1 := by simp [Zsqrtd.norm_def, hi, hr]
            exact ha (unit_of_norm_one a this)
        · have hare2 : a.re ^ 2 ≤ 1 := by
            norm_num at hae
            rw [pow_two]
            nlinarith
          have hrelo : -2 < a.re := by nlinarith [sq_nonneg (a.re + 2)]
          have hrehi : a.re < 2 := by nlinarith [sq_nonneg (a.re - 2)]
          interval_cases hr : a.re
          · have haeq : a.norm = n + 1 := by simp [Zsqrtd.norm_def, hi, hr]; ring
            rw [haeq] at hm
            have hc : (n + 1) * 1 = (n + 1) * b.norm := by simpa using hm
            have : b.norm = 1 := (mul_left_cancel₀ (by omega : n + 1 ≠ 0) hc).symm
            exact hb (unit_of_norm_one b this)
          · have haeq : a.norm = n := by simp [Zsqrtd.norm_def, hi, hr]
            rw [haeq] at hm
            have hnb : n * 2 ≤ n * b.norm :=
              mul_le_mul_of_nonneg_left hb2 (by omega)
            omega
          · have haeq : a.norm = n + 1 := by simp [Zsqrtd.norm_def, hi, hr]; ring
            rw [haeq] at hm
            have hc : (n + 1) * 1 = (n + 1) * b.norm := by simpa using hm
            have : b.norm = 1 := (mul_left_cancel₀ (by omega : n + 1 ≠ 0) hc).symm
            exact hb (unit_of_norm_one b this)
