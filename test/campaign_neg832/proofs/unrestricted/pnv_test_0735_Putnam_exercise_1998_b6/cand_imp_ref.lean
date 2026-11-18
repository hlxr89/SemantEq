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
  let T : ℤ := |a| + |b| + |c| + 1
  obtain ⟨k, hk⟩ :=
    @dummy_assumed (3*T + a) (3*T^2 + 2*a*T + b)
      (T^3 + a*T^2 + b*T + c)
  let n : ℤ := (k : ℤ) + T
  have hT : 0 < T := by
    dsimp [T]
    have ha : 0 ≤ |a| := abs_nonneg a
    have hb : 0 ≤ |b| := abs_nonneg b
    have hc : 0 ≤ |c| := abs_nonneg c
    omega
  have hnT : T ≤ n := by simp [n]
  have hn : 0 < n := lt_of_lt_of_le hT hnT
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  have ha : -|a| ≤ a := neg_abs_le a
  have hb : -|b| ≤ b := neg_abs_le b
  have hc : -|c| ≤ c := neg_abs_le c
  have hn1 : 1 ≤ n := by omega
  have hna : |b| + |c| + 1 ≤ n + a := by
    dsimp [T] at hnT
    omega
  have hn0 : 0 ≤ n := by omega
  have hbn : -(|b| * n) ≤ b * n := by
    nlinarith [mul_nonneg (show 0 ≤ n by omega) (show 0 ≤ b + |b| by omega)]
  have hnn : n ≤ n^2 := by nlinarith
  have hbn' : |b| * n ≤ |b| * n^2 := by
    exact mul_le_mul_of_nonneg_left hnn (abs_nonneg b)
  have hcn' : |c| ≤ |c| * n^2 := by
    have : 1 ≤ n^2 := by nlinarith
    nlinarith [mul_nonneg (abs_nonneg c) (sub_nonneg.mpr this)]
  have hpos : 0 < n^3 + a*n^2 + b*n + c := by
    have hmain : n^2 * (|b| + |c| + 1) ≤ n^2 * (n + a) :=
      mul_le_mul_of_nonneg_left hna (sq_nonneg n)
    nlinarith
  have hm0R : (0 : ℝ) ≤ m := by
    rw [← hm]
    exact Real.sqrt_nonneg _
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast hm0R
  let q : ℕ := m.toNat
  have hq : (q : ℤ) = m := by simpa [q] using Int.toNat_of_nonneg hm0
  apply hk
  refine ⟨q, ?_⟩
  have hsqrt_sq :
      (Real.sqrt ((n : ℝ)^3 + (a : ℝ)*(n : ℝ)^2 + (b : ℝ)*(n : ℝ) + c))^2 =
        (n : ℝ)^3 + (a : ℝ)*(n : ℝ)^2 + (b : ℝ)*(n : ℝ) + c := by
    rw [Real.sq_sqrt]
    exact_mod_cast (le_of_lt hpos)
  have hm_sq : m^2 = n^3 + a*n^2 + b*n + c := by
    rw [hm] at hsqrt_sq
    exact_mod_cast hsqrt_sq
  change (q : ℤ)^2 = (k : ℤ)^3 + (3*T + a) * (k : ℤ)^2 +
    (3*T^2 + 2*a*T + b) * (k : ℤ) + (T^3 + a*T^2 + b*T + c)
  rw [hq, hm_sq]
  dsimp [n]
  ring
