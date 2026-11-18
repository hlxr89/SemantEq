import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b c : ℤ} : ∃ n : ℕ, ¬∃ m : ℕ, m^2 = n^3 + a * n^2 + b * n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let t : ℤ := |a| + |b| + |c| + 1
  have hna : 0 ≤ |a| := abs_nonneg a
  have hnb : 0 ≤ |b| := abs_nonneg b
  have hnc : 0 ≤ |c| := abs_nonneg c
  have ht : 0 < t := by
    dsimp [t]
    omega
  have ha : -t < a := by
    dsimp [t]
    have := neg_abs_le a
    omega
  have hb : -t < b := by
    dsimp [t]
    have := neg_abs_le b
    omega
  have hc : -t < c := by
    dsimp [t]
    have := neg_abs_le c
    omega
  have hA : 0 ≤ a + 3 * t := by omega
  have hB : 0 ≤ b + 2 * a * t + 3 * t ^ 2 := by
    have hmul : 0 ≤ (a + t) * t := mul_nonneg (by omega) (by omega)
    nlinarith
  have hC : 0 < t ^ 3 + a * t ^ 2 + b * t + c := by
    have hat : 0 ≤ (a + t) * t ^ 2 := mul_nonneg (by omega) (sq_nonneg t)
    have hbt : 0 ≤ (b + t) * t := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (t - 1)]
  obtain ⟨k, hk⟩ := dummy_assumed
    (a := a + 3 * t) (b := b + 2 * a * t + 3 * t ^ 2)
    (c := t ^ 3 + a * t ^ 2 + b * t + c)
  refine ⟨(k : ℤ) + t, by omega, ?_⟩
  rintro ⟨m, hm⟩
  have hq_nonneg : 0 ≤ (k : ℤ) ^ 3 + (a + 3 * t) * (k : ℤ) ^ 2 +
      (b + 2 * a * t + 3 * t ^ 2) * k + (t ^ 3 + a * t ^ 2 + b * t + c) := by
    positivity
  have hshift : ((k : ℤ) + t) ^ 3 + a * ((k : ℤ) + t) ^ 2 + b * ((k : ℤ) + t) + c =
      (k : ℤ) ^ 3 + (a + 3 * t) * (k : ℤ) ^ 2 +
        (b + 2 * a * t + 3 * t ^ 2) * k + (t ^ 3 + a * t ^ 2 + b * t + c) := by
    ring
  have hrad_nonneg_int : 0 ≤ ((k : ℤ) + t) ^ 3 + a * ((k : ℤ) + t) ^ 2 + b * ((k : ℤ) + t) + c := by
    rw [hshift]
    exact hq_nonneg
  have hm_nonneg_real : (0 : ℝ) ≤ (m : ℝ) := by
    rw [← hm]
    exact Real.sqrt_nonneg _
  have hm_nonneg : 0 ≤ m := by
    exact_mod_cast hm_nonneg_real
  apply hk
  refine ⟨m.toNat, ?_⟩
  have hm_cast : (m.toNat : ℤ) = m := by omega
  rw [show (m.toNat : ℤ) ^ 2 = m ^ 2 by rw [hm_cast]]
  have hrad_nonneg_real : (0 : ℝ) ≤
      ((k : ℤ) + t) ^ 3 + a * ((k : ℤ) + t) ^ 2 + b * ((k : ℤ) + t) + c := by
    exact_mod_cast hrad_nonneg_int
  have hsquare_real : (m : ℝ) ^ 2 =
      ((k : ℤ) + t) ^ 3 + a * ((k : ℤ) + t) ^ 2 + b * ((k : ℤ) + t) + c := by
    rw [← hm]
    norm_num
    exact Real.sq_sqrt hrad_nonneg_real
  have hsquare_int : m ^ 2 =
      ((k : ℤ) + t) ^ 3 + a * ((k : ℤ) + t) ^ 2 + b * ((k : ℤ) + t) + c := by
    exact_mod_cast hsquare_real
  rw [hsquare_int, hshift]
