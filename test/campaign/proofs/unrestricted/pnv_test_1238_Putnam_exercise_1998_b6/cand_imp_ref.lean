import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b c : ℤ} : ∃ (n : ℕ) (hn : 0 < n), ¬ ∃ (m : ℤ), n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let k : ℤ := |a| + |b| + |c| + 1
  rcases dummy_assumed
      (a := 3 * k + a)
      (b := 3 * k ^ 2 + 2 * a * k + b)
      (c := k ^ 3 + a * k ^ 2 + b * k + c) with ⟨x, hx, hxsq⟩
  let n : ℤ := (x : ℤ) + k
  have hxz : (0 : ℤ) < x := by exact_mod_cast hx
  have ha0 : 0 ≤ |a| := abs_nonneg a
  have hb0 : 0 ≤ |b| := abs_nonneg b
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hk : 1 ≤ k := by
    dsimp [k]
    omega
  have hn : 0 < n := by
    dsimp [n]
    omega
  have hnlarge : |a| + |b| + |c| + 1 ≤ n := by
    dsimp [n, k]
    omega
  have hn1 : 1 ≤ n := by omega
  have hn_sq : n ≤ n ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hn) (sub_nonneg.mpr hn1)]
  have hn_sq_one : 1 ≤ n ^ 2 := by nlinarith
  have hgap : |b| + |c| + 1 ≤ n - |a| := by omega
  have hgap_mul := mul_le_mul_of_nonneg_right hgap (sq_nonneg n)
  have hb_mul := mul_le_mul_of_nonneg_left hn_sq (abs_nonneg b)
  have hc_mul := mul_le_mul_of_nonneg_left hn_sq_one (abs_nonneg c)
  have ha_term := mul_le_mul_of_nonneg_right (neg_abs_le a) (sq_nonneg n)
  have hb_term := mul_le_mul_of_nonneg_right (neg_abs_le b) (le_of_lt hn)
  have hc_term : -|c| ≤ c := neg_abs_le c
  have hpolypos : 0 < n ^ 3 + a * n ^ 2 + b * n + c := by
    nlinarith
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  apply hxsq
  refine ⟨m, ?_⟩
  have hp_real : (0 : ℝ) ≤ (n : ℝ) ^ 3 + (a : ℝ) * (n : ℝ) ^ 2 +
      (b : ℝ) * (n : ℝ) + c := by
    exact_mod_cast (le_of_lt hpolypos)
  have hsqrt_sq : (Real.sqrt (n ^ 3 + a * n ^ 2 + b * n + c)) ^ 2 =
      (n : ℝ) ^ 3 + (a : ℝ) * (n : ℝ) ^ 2 + (b : ℝ) * (n : ℝ) + c := by
    exact Real.sq_sqrt hp_real
  have hm_sq : (n ^ 3 + a * n ^ 2 + b * n + c : ℤ) = m ^ 2 := by
    rw [hm] at hsqrt_sq
    exact_mod_cast hsqrt_sq.symm
  change (x : ℤ) ^ 3 + (3 * k + a) * (x : ℤ) ^ 2 +
      (3 * k ^ 2 + 2 * a * k + b) * (x : ℤ) +
      (k ^ 3 + a * k ^ 2 + b * k + c) = m ^ 2
  rw [← hm_sq]
  dsimp [n]
  ring
