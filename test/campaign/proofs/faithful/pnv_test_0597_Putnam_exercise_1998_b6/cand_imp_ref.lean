import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b c : ℤ} : ∃ n : ℕ, ¬ ∃ m : ℤ, m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let k : ℤ := |a| + |b| + |c| + 1
  obtain ⟨t, ht⟩ := dummy_assumed (a := 3 * k + a)
    (b := 3 * k ^ 2 + 2 * a * k + b)
    (c := k ^ 3 + a * k ^ 2 + b * k + c)
  let n : ℤ := (t : ℤ) + k
  have hk : 0 < k := by
    dsimp [k]
    have := abs_nonneg a
    have := abs_nonneg b
    have := abs_nonneg c
    omega
  have htn : 0 ≤ (t : ℤ) := by positivity
  have hnk : k ≤ n := by simp [n]
  have hn : 0 < n := lt_of_lt_of_le hk hnk
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  apply ht
  refine ⟨m, ?_⟩
  have ha : -|a| ≤ a := neg_abs_le a
  have hb : -|b| ≤ b := neg_abs_le b
  have hc : -|c| ≤ c := neg_abs_le c
  have hpoly : 0 ≤ n^3 + a*n^2 + b*n + c := by
    have habs_a := abs_nonneg a
    have habs_b := abs_nonneg b
    have habs_c := abs_nonneg c
    have hna : |a| < n := by dsimp [k] at hnk; omega
    have hnb : |b| < n := by dsimp [k] at hnk; omega
    have hnc : |c| < n := by dsimp [k] at hnk; omega
    have pa := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg n)
    have pb := mul_nonneg (sub_nonneg.mpr hb) (le_of_lt hn)
    have p1 := mul_nonneg (sq_nonneg n) (show 0 ≤ n - |a| - 1 by omega)
    have p2 := mul_nonneg (le_of_lt hn) (show 0 ≤ n - |b| - 1 by omega)
    nlinarith
  have hsquare : (m : ℝ) ^ 2 =
      (n : ℝ)^3 + (a : ℝ)*(n : ℝ)^2 + (b : ℝ)*(n : ℝ) + (c : ℝ) := by
    rw [← hm]
    exact Real.sq_sqrt (by exact_mod_cast hpoly)
  have hsquareZ : m ^ 2 = n^3 + a*n^2 + b*n + c := by
    exact_mod_cast hsquare
  calc
    m ^ 2 = n^3 + a*n^2 + b*n + c := hsquareZ
    _ = (t : ℤ) ^ 3 + (3 * k + a) * (t : ℤ) ^ 2 +
        (3 * k ^ 2 + 2 * a * k + b) * (t : ℤ) +
        (k ^ 3 + a * k ^ 2 + b * k + c) := by simp [n]; ring
    _ = t ^ 3 + (3 * k + a) * t ^ 2 +
        (3 * k ^ 2 + 2 * a * k + b) * t +
        (k ^ 3 + a * k ^ 2 + b * k + c) := by norm_cast
