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
  let t : ℤ := |a| + |b| + |c| + 1
  obtain ⟨n, hn, hnsq⟩ := dummy_assumed (3 * t + a) (3 * t ^ 2 + 2 * a * t + b)
    (t ^ 3 + a * t ^ 2 + b * t + c)
  let x : ℤ := (n : ℤ) + t
  have ht : 0 < t := by
    dsimp [t]
    have ha : 0 ≤ |a| := abs_nonneg a
    have hb : 0 ≤ |b| := abs_nonneg b
    have hc : 0 ≤ |c| := abs_nonneg c
    omega
  have hnx : 0 < (n : ℤ) := by exact_mod_cast hn
  have hx : 0 < x := by
    dsimp [x]
    omega
  have hid :
      x ^ 3 + a * x ^ 2 + b * x + c =
        (n : ℤ) ^ 3 + (3 * t + a) * (n : ℤ) ^ 2 +
          (3 * t ^ 2 + 2 * a * t + b) * (n : ℤ) +
            (t ^ 3 + a * t ^ 2 + b * t + c) := by
    dsimp [x]
    ring
  have hval_nonneg : 0 ≤ x ^ 3 + a * x ^ 2 + b * x + c := by
    have hxa : |a| ≤ x := by
      dsimp [x, t]
      have hb : 0 ≤ |b| := abs_nonneg b
      have hc : 0 ≤ |c| := abs_nonneg c
      omega
    have hxb : |b| ≤ x := by
      dsimp [x, t]
      have ha : 0 ≤ |a| := abs_nonneg a
      have hc : 0 ≤ |c| := abs_nonneg c
      omega
    have hxc : |c| ≤ x := by
      dsimp [x, t]
      have ha : 0 ≤ |a| := abs_nonneg a
      have hb : 0 ≤ |b| := abs_nonneg b
      omega
    have ha : -|a| ≤ a := neg_abs_le a
    have hb : -|b| ≤ b := neg_abs_le b
    have hc : -|c| ≤ c := neg_abs_le c
    have hx0 : 0 ≤ x := le_of_lt hx
    have hx1 : 1 ≤ x := by omega
    have hx2x : x ≤ x ^ 2 := by nlinarith
    have hsum : |a| + |b| + |c| ≤ x - 1 := by
      dsimp [x, t]
      omega
    have hcoeff :
        -(|a| * x ^ 2 + |b| * x + |c|) ≤ a * x ^ 2 + b * x + c := by
      nlinarith [mul_nonneg (show 0 ≤ a + |a| by omega) (sq_nonneg x),
        mul_nonneg (show 0 ≤ b + |b| by omega) hx0]
    have hterms : |a| * x ^ 2 + |b| * x + |c| ≤
        (|a| + |b| + |c|) * x ^ 2 := by
      have hx2one : 1 ≤ x ^ 2 := by nlinarith
      nlinarith [mul_nonneg (abs_nonneg b) (sub_nonneg.mpr hx2x),
        mul_nonneg (abs_nonneg c) (sub_nonneg.mpr hx2one)]
    have htop : (|a| + |b| + |c|) * x ^ 2 ≤ (x - 1) * x ^ 2 := by
      exact mul_le_mul_of_nonneg_right hsum (sq_nonneg x)
    nlinarith
  refine ⟨x, hx, ?_⟩
  rintro ⟨m, hm⟩
  apply hnsq
  refine ⟨m, ?_⟩
  have hreal_nonneg :
      0 ≤ (x : ℝ) ^ 3 + (a : ℝ) * (x : ℝ) ^ 2 + (b : ℝ) * x + c := by
    exact_mod_cast hval_nonneg
  have hsqrt_sq := Real.sq_sqrt hreal_nonneg
  have hm_sq : (m : ℝ) ^ 2 = (x ^ 3 + a * x ^ 2 + b * x + c : ℤ) := by
    calc
      (m : ℝ) ^ 2 = (Real.sqrt (x ^ 3 + a * x ^ 2 + b * x + c)) ^ 2 := by rw [hm]
      _ = (x : ℝ) ^ 3 + (a : ℝ) * (x : ℝ) ^ 2 + (b : ℝ) * x + c := hsqrt_sq
      _ = (x ^ 3 + a * x ^ 2 + b * x + c : ℤ) := by norm_num
  have hm_sq_int : m ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c := by
    exact_mod_cast hm_sq
  rw [hid] at hm_sq_int
  simpa using hm_sq_int
