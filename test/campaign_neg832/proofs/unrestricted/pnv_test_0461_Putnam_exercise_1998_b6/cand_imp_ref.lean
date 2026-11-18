import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) (h : ∃ n : ℤ, (n : ℝ)^3 + (a * n^2) + (b * n) + c ≠ (n : ℝ)) : ∃ n : ℤ, 0 < n ∧ (n : ℝ)^3 + (a * n^2) + (b * n) + c ≠ (n : ℝ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let F : ℤ → ℤ := fun n => n^3 + a*n^2 + b*n + c
  have between_squares (n q : ℤ) (hn : 0 < n) (hq : 0 ≤ q)
      (hl : q^2 < F n) (hu : F n < (q+1)^2) :
      ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
    refine ⟨n, hn, ?_⟩
    rintro ⟨m, hm⟩
    have hFn : (0 : ℝ) ≤ F n := by
      exact_mod_cast (le_trans (sq_nonneg q) hl.le)
    have hlo : (q : ℝ) < Real.sqrt (F n) := by
      apply Real.lt_sqrt_of_sq_lt
      exact_mod_cast hl
    have hhi : Real.sqrt (F n) < (q + 1 : ℤ) := by
      rw [Real.sqrt_lt hFn]
      · exact_mod_cast hu
      · exact_mod_cast (by omega : (0 : ℤ) ≤ q + 1)
    have hm' : Real.sqrt (F n) = (m : ℝ) := by
      simpa only [F, Int.cast_add, Int.cast_mul, Int.cast_pow] using hm
    rw [hm'] at hlo hhi
    have hlo' : q < m := by exact_mod_cast hlo
    have hhi' : m < q + 1 := by exact_mod_cast hhi
    omega
  let D : ℤ := 4*b - a^2
  let x : ℤ := |D| + |c| + |a| + 2
  let q : ℤ := 8*x^3 + a*x
  have hx : 2 ≤ x := by
    dsimp [x]
    have := abs_nonneg D
    have := abs_nonneg c
    have := abs_nonneg a
    omega
  have hx0 : 0 < x := by omega
  have hDx : |D| < x := by
    dsimp [x]
    have := abs_nonneg c
    have := abs_nonneg a
    omega
  have hcx : |c| < x := by
    dsimp [x]
    have := abs_nonneg D
    have := abs_nonneg a
    omega
  have hax : |a| < x := by
    dsimp [x]
    have := abs_nonneg D
    have := abs_nonneg c
    omega
  have hDabslo : -|D| ≤ D := neg_abs_le D
  have hDabshi : D ≤ |D| := le_abs_self D
  have hcabslo : -|c| ≤ c := neg_abs_le c
  have hcabshi : c ≤ |c| := le_abs_self c
  have haabslo : -|a| ≤ a := neg_abs_le a
  have haabshi : a ≤ |a| := le_abs_self a
  have hDlo : -x < D := by omega
  have hDhi : D < x := by omega
  have hclo : -x < c := by omega
  have hchi : c < x := by omega
  have halo : -x < a := by omega
  have haxmul : -x*x < a*x := by
    exact mul_lt_mul_of_pos_right halo hx0
  have hq : 0 < q := by
    dsimp [q]
    nlinarith only [haxmul, hx, sq_nonneg x, mul_self_nonneg (x-1)]
  have hqx : x < q := by
    dsimp [q]
    nlinarith only [haxmul, hx, sq_nonneg x, mul_self_nonneg (x-1)]
  have hidentity : F (4*x^2) = q^2 + D*x^2 + c := by
    dsimp [F, q, D]
    ring
  by_cases hDpos : 0 < D
  · have hD1 : 1 ≤ D := by omega
    have hdelta0 : 0 < D*x^2+c := by
      nlinarith only [hD1, hclo, hx, sq_nonneg x, mul_self_nonneg (x-1)]
    have hlow : q^2 < F (4*x^2) := by
      rw [hidentity]
      convert add_lt_add_left hdelta0 (q^2) using 1 <;> ring
    have hDmul : D*x^2 < x*x^2 := by
      exact mul_lt_mul_of_pos_right hDhi (sq_pos_of_pos hx0)
    have hdeltaGap : D*x^2+c < 2*q+1 := by
      dsimp [q]
      nlinarith only [hDmul, hchi, haxmul, hx, sq_nonneg x,
        mul_self_nonneg (x-1)]
    have hupp : F (4*x^2) < (q+1)^2 := by
      rw [hidentity]
      convert add_lt_add_left hdeltaGap (q^2) using 1 <;> ring
    exact between_squares (4*x^2) q (by positivity) hq.le hlow hupp
  by_cases hDneg : D < 0
  · have hD1 : D ≤ -1 := by omega
    have hdeltaNeg : D*x^2+c < 0 := by
      nlinarith only [hD1, hchi, hx, sq_nonneg x, mul_self_nonneg (x-1)]
    have hDmul : -x*x^2 < D*x^2 := by
      exact mul_lt_mul_of_pos_right hDlo (sq_pos_of_pos hx0)
    have hdeltaGap : -2*q+1 < D*x^2+c := by
      dsimp [q]
      nlinarith only [hDmul, hclo, haxmul, hx, sq_nonneg x,
        mul_self_nonneg (x-1)]
    have hlow : (q-1)^2 < F (4*x^2) := by
      rw [hidentity]
      convert add_lt_add_left hdeltaGap (q^2) using 1 <;> ring
    have hupp : F (4*x^2) < q^2 := by
      rw [hidentity]
      convert add_lt_add_left hdeltaNeg (q^2) using 1 <;> ring
    exact between_squares (4*x^2) (q-1) (by positivity) (by omega) hlow (by simpa using hupp)
  have hDzero : D = 0 := by omega
  by_cases hcpos : 0 < c
  · have hlow : q^2 < F (4*x^2) := by
      rw [hidentity, hDzero]
      convert add_lt_add_left hcpos (q^2) using 1 <;> ring
    have hcGap : c < 2*q+1 := by omega
    have hupp : F (4*x^2) < (q+1)^2 := by
      rw [hidentity, hDzero]
      convert add_lt_add_left hcGap (q^2) using 1 <;> ring
    exact between_squares (4*x^2) q (by positivity) hq.le hlow hupp
  by_cases hcneg : c < 0
  · have hcGap : -2*q+1 < c := by omega
    have hlow : (q-1)^2 < F (4*x^2) := by
      rw [hidentity, hDzero]
      convert add_lt_add_left hcGap (q^2) using 1 <;> ring
    have hupp : F (4*x^2) < q^2 := by
      rw [hidentity, hDzero]
      convert add_lt_add_left hcneg (q^2) using 1 <;> ring
    exact between_squares (4*x^2) (q-1) (by positivity) (by omega) hlow (by simpa using hupp)
  have hczero : c = 0 := by omega
  have ha2 : a^2 = 4*b := by dsimp [D] at hDzero; omega
  have haeven : Even a := by
    rw [← Int.even_pow' (by norm_num : (2 : ℕ) ≠ 0)]
    refine ⟨2*b, ?_⟩
    nlinarith only [ha2]
  obtain ⟨d, hd⟩ := haeven
  have hb : b = d^2 := by
    rw [hd] at ha2
    nlinarith only [ha2]
  by_cases hd2 : d = -2
  · refine ⟨3, by norm_num, ?_⟩
    rintro ⟨m, hm⟩
    have hm3 : Real.sqrt (3 : ℝ) = (m : ℝ) := by
      rw [← hm]
      congr 1
      norm_num [hczero, hd, hb, hd2]
    exact (Nat.prime_three.irrational_sqrt.ne_rational m 1) (by simpa using hm3)
  · refine ⟨2, by norm_num, ?_⟩
    rintro ⟨m, hm⟩
    have hk : d + 2 ≠ 0 := by omega
    have hsqrt : Real.sqrt (2 : ℝ) * |(d + 2 : ℤ)| = (m : ℝ) := by
      calc
        Real.sqrt (2 : ℝ) * |(d + 2 : ℤ)| = Real.sqrt ((2 : ℝ) * ((d + 2 : ℤ) : ℝ)^2) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs]
          norm_cast
        _ = (m : ℝ) := by
          rw [← hm]
          congr 1
          norm_num [hczero, hd, hb]
          ring
    have habs : (|(d + 2 : ℤ)| : ℝ) ≠ 0 := by exact_mod_cast (abs_ne_zero.mpr hk)
    have hsqrt' : Real.sqrt (2 : ℝ) = (m : ℝ) / (|(d + 2 : ℤ)| : ℝ) := by
      apply (eq_div_iff habs).2
      simpa [mul_comm] using hsqrt
    exact (irrational_sqrt_two.ne_rational m |d+2|) (by
      simpa only [Int.cast_abs] using hsqrt')
