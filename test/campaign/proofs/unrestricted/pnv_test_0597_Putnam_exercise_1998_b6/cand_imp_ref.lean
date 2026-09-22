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
  let K : ℤ := |a| + |b| + |c| + 1
  obtain ⟨k, hk⟩ := dummy_assumed
    (a := 3 * K + a)
    (b := 3 * K ^ 2 + 2 * a * K + b)
    (c := K ^ 3 + a * K ^ 2 + b * K + c)
  let n : ℤ := (k : ℤ) + K
  have habsa : 0 ≤ |a| := abs_nonneg a
  have habsb : 0 ≤ |b| := abs_nonneg b
  have habsc : 0 ≤ |c| := abs_nonneg c
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hK : 0 < K := by
    dsimp [K]
    omega
  have hn : 0 < n := by
    dsimp [n]
    omega
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  have ha : -(n - 1) ≤ a := by
    have : |a| ≤ n - 1 := by
      dsimp [n, K]
      omega
    exact (abs_le.mp this).1
  have hb : -(n - 1) ≤ b := by
    have : |b| ≤ n - 1 := by
      dsimp [n, K]
      omega
    exact (abs_le.mp this).1
  have hc : -(n - 1) ≤ c := by
    have : |c| ≤ n - 1 := by
      dsimp [n, K]
      omega
    exact (abs_le.mp this).1
  have hpoly : 0 ≤ n ^ 3 + a * n ^ 2 + b * n + c := by
    nlinarith [sq_nonneg n, sq_nonneg (n - 1),
      mul_nonneg (show 0 ≤ a + (n - 1) by omega) (sq_nonneg n),
      mul_nonneg (show 0 ≤ b + (n - 1) by omega) (show 0 ≤ n by omega)]
  have hsquare_real : ((m : ℝ) ^ 2) =
      (n : ℝ) ^ 3 + (a : ℝ) * (n : ℝ) ^ 2 + (b : ℝ) * n + c := by
    have hs := congrArg (fun x : ℝ => x ^ 2) hm.symm
    change (m : ℝ) ^ 2 = (Real.sqrt
      ((n : ℝ) ^ 3 + (a : ℝ) * (n : ℝ) ^ 2 + (b : ℝ) * n + c)) ^ 2 at hs
    have hpoly_real : (0 : ℝ) ≤
        (n : ℝ) ^ 3 + (a : ℝ) * (n : ℝ) ^ 2 + (b : ℝ) * n + c := by
      exact_mod_cast hpoly
    rw [Real.sq_sqrt hpoly_real] at hs
    simpa using hs
  have hsquare : m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
    exact_mod_cast hsquare_real
  apply hk
  refine ⟨m, ?_⟩
  rw [hsquare]
  dsimp [n]
  ring
