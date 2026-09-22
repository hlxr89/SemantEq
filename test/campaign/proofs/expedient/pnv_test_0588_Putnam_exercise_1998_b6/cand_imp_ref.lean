import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) : ∃ n : ℕ, 0 < n ∧ ¬ ∃ k : ℤ, k^2 = n^3 + a * n^2 + b * n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let d : ℤ := |a| + |b| + |c| + 1
  obtain ⟨t, ht, htnsq⟩ := dummy_assumed
    (a + 3 * d) (b + 2 * a * d + 3 * d^2) (d^3 + a * d^2 + b * d + c)
  let n : ℤ := t + d
  have hd : 0 < d := by
    dsimp [d]
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    have hc := abs_nonneg c
    omega
  have htd : 0 < (t : ℤ) := by exact_mod_cast ht
  have hn : 0 < n := by dsimp [n]; omega
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  apply htnsq
  refine ⟨m, ?_⟩
  have ha := le_abs_self a
  have hb := le_abs_self b
  have hc := le_abs_self c
  have ha0 := abs_nonneg a
  have hb0 := abs_nonneg b
  have hc0 := abs_nonneg c
  have hsum : |a| + |b| + |c| < n := by dsimp [n, d]; omega
  have hp : 0 ≤ n^3 + a*n^2 + b*n + c := by
    have hn1 : 1 ≤ n := by omega
    have hnquad : n ≤ n^2 := by
      nlinarith [mul_nonneg (le_of_lt hn) (sub_nonneg.mpr hn1)]
    have hnquad1 : 1 ≤ n^2 := by nlinarith
    have hdiff : |b| + |c| + 1 ≤ n - |a| := by omega
    have hbig := mul_le_mul_of_nonneg_left hdiff (sq_nonneg n)
    have hbn := mul_le_mul_of_nonneg_left hnquad hb0
    have hc1 := mul_le_mul_of_nonneg_left hnquad1 hc0
    have hmain : |b| * n + |c| ≤ n^2 * (n - |a|) := by nlinarith
    have halow := mul_le_mul_of_nonneg_right (neg_abs_le a) (sq_nonneg n)
    have hblow := mul_le_mul_of_nonneg_right (neg_abs_le b) (le_of_lt hn)
    nlinarith [neg_abs_le c]
  have hpR : (0 : ℝ) ≤ (n : ℝ)^3 + a*(n : ℝ)^2 + b*n + c := by exact_mod_cast hp
  have hsquare : (m : ℝ)^2 = n^3 + a*n^2 + b*n + c := by
    rw [← hm]
    exact Real.sq_sqrt hpR
  have hsquareZ : m^2 = n^3 + a*n^2 + b*n + c := by exact_mod_cast hsquare
  dsimp [n] at hsquareZ ⊢
  norm_num at hsquareZ ⊢
  nlinarith
