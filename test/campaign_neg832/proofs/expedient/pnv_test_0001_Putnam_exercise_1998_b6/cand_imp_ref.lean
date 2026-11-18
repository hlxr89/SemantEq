import Mathlib

set_option maxHeartbeats 800000

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) : ∃ (n : ℕ) (H : 0 < n), √(n^3 + a*n^2 + b*n + c) ≠ n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  by_contra! h
  let D : ℤ := 4*b - a^2
  have square_eq (k : ℤ) (hk2 : 2 < k) (hka : |a| < k)
      (hkD : |D| < k) (hkc : |c| < k) : D*k^2 + c = 0 := by
    let q : ℤ := 8*k^3 + a*k
    have hk0 : 0 < k := by omega
    have hk20 : 0 ≤ k^2 := sq_nonneg k
    have hk2pos : 0 < k^2 := sq_pos_of_pos hk0
    have hak : -k < a ∧ a < k := (abs_lt.mp hka)
    have hDk : -k < D ∧ D < k := (abs_lt.mp hkD)
    have hck : -k < c ∧ c < k := (abs_lt.mp hkc)
    have ha_mul : -k*k < a*k := by nlinarith
    have hD_mul_lo : -k*k^2 < D*k^2 := by
      exact mul_lt_mul_of_pos_right hDk.1 hk2pos
    have hD_mul_hi : D*k^2 < k*k^2 := by
      exact mul_lt_mul_of_pos_right hDk.2 hk2pos
    have hq0 : 0 < q := by
      dsimp [q]
      nlinarith [sq_nonneg (k - 1)]
    have hlo : -(2*q - 1) < D*k^2 + c := by
      dsimp [q]
      nlinarith [sq_nonneg (k - 1)]
    have hhi : D*k^2 + c < 2*q + 1 := by
      dsimp [q]
      nlinarith [sq_nonneg (k - 1)]
    obtain ⟨m, hm⟩ := h ((2*k)^2) (by positivity)
    have hm0 : 0 ≤ m := by
      exact_mod_cast (hm ▸ Real.sqrt_nonneg _)
    let x : ℝ := ((2*k)^2 : ℤ)
    have hm' : Real.sqrt (x^3 + (a:ℝ)*x^2 + (b:ℝ)*x + c) = m := by
      simpa [x] using hm
    have hradI : 0 ≤ ((2*k)^2)^3 + a*((2*k)^2)^2 + b*((2*k)^2) + c := by
      have hid : ((2*k)^2)^3 + a*((2*k)^2)^2 + b*((2*k)^2) + c =
          q^2 + (D*k^2+c) := by dsimp [q, D]; ring
      rw [hid]
      nlinarith [sq_nonneg (q-1)]
    have hrad : 0 ≤ x^3 + (a:ℝ)*x^2 + (b:ℝ)*x + c := by
      dsimp [x]
      exact_mod_cast hradI
    have hsquareR : (m : ℝ)^2 = x^3 + (a:ℝ)*x^2 + (b:ℝ)*x + c := by
      calc
        (m : ℝ)^2 = (Real.sqrt (x^3 + (a:ℝ)*x^2 + (b:ℝ)*x + c))^2 := by rw [hm']
        _ = _ := Real.sq_sqrt hrad
    have hsquare : m^2 = q^2 + (D*k^2 + c) := by
      have hsquare0 : m^2 = ((2*k)^2)^3 + a*((2*k)^2)^2 + b*((2*k)^2) + c := by
        dsimp [x] at hsquareR
        exact_mod_cast hsquareR
      calc
        m^2 = ((2*k)^2)^3 + a*((2*k)^2)^2 + b*((2*k)^2) + c := hsquare0
        _ = q^2 + (D*k^2 + c) := by dsimp [q, D]; ring
    by_cases hmq : m = q
    · subst m
      nlinarith
    · rcases lt_or_gt_of_ne hmq with hmq | hmq
      · have hm_le : m ≤ q - 1 := by omega
        have hm_sq : m^2 ≤ (q-1)^2 := by nlinarith
        nlinarith
      · have hq_le : q + 1 ≤ m := by omega
        have hq_sq : (q+1)^2 ≤ m^2 := by nlinarith
        nlinarith
  obtain ⟨K, hK⟩ : ∃ K : ℤ, max (max |a| |D|) |c| + 3 < K := exists_int_gt _
  have hK2 : 2 < K := by
    have : 0 ≤ max (max |a| |D|) |c| := by positivity
    omega
  have hmax : max (max |a| |D|) |c| < K := by omega
  have hKa : |a| < K := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hmax
  have hKD : |D| < K := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hmax
  have hKc : |c| < K := lt_of_le_of_lt (le_max_right _ _) hmax
  have eK := square_eq K hK2 hKa hKD hKc
  have eK1 := square_eq (K+1) (by omega) (lt_trans hKa (by omega))
    (lt_trans hKD (by omega)) (lt_trans hKc (by omega))
  have hD0 : D = 0 := by nlinarith
  have hc0 : c = 0 := by nlinarith
  have haeven : Even a := by
    dsimp [D] at hD0
    apply even_iff_two_dvd.mpr
    apply (show Prime (2 : ℤ) by norm_num).dvd_of_dvd_pow (n := 2)
    use 2*b
    nlinarith
  obtain ⟨r, hr⟩ := haeven
  have har : a = 2*r := by omega
  have hbr : b = r^2 := by
    dsimp [D] at hD0
    rw [har] at hD0
    nlinarith
  by_cases hz : (2 : ℤ) + r = 0
  · obtain ⟨m, hm⟩ := h 3 (by norm_num)
    have hirr : Irrational (Real.sqrt (3 : ℝ)) := Nat.prime_three.irrational_sqrt
    rw [har, hbr, hc0] at hm
    have hrval : r = -2 := by omega
    subst r
    norm_num at hm
    exact hirr.ne_int m hm
  · obtain ⟨m, hm⟩ := h 2 (by norm_num)
    have hirr : Irrational (Real.sqrt (2 : ℝ)) := irrational_sqrt_two
    rw [har, hbr, hc0] at hm
    have hm2 : Real.sqrt ((2 : ℝ) * (2+r)^2) = m := by
      have hpoly : ((2:ℝ)^3 + (2*r:ℤ)*(2:ℝ)^2 + (r^2:ℤ)*(2:ℝ) + (0:ℤ)) =
          (2:ℝ) * (2+r)^2 := by norm_num; ring
      rw [← hpoly]
      exact hm
    have hs : Real.sqrt ((2 : ℝ) * (2+r)^2) = Real.sqrt 2 * |(2+r : ℝ)| := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
    have habs : |(2+r : ℝ)| = (|(2+r : ℤ)| : ℝ) := by norm_cast
    rw [hs, habs] at hm2
    apply hirr.ne_rational m |(2+r : ℤ)|
    have hnzI : |(2+r : ℤ)| ≠ 0 := abs_ne_zero.mpr hz
    have hnzR : ((|(2+r : ℤ)| : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hnzI
    rw [eq_div_iff hnzR]
    simpa [mul_comm] using hm2
