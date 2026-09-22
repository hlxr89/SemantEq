import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) : ∃ n : ℕ, 0 < n ∧ ¬(∃ m : ℤ, m^2 = n^3 + a * n^2 + b * n + c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let k : ℤ := |a| + |b| + |c| + 1
  obtain ⟨n, hn, hnonsq⟩ := dummy_assumed (3*k + a) (3*k^2 + 2*a*k + b)
    (k^3 + a*k^2 + b*k + c)
  let N : ℤ := n + k
  have hk : 0 < k := by dsimp [k]; positivity
  have hnZ : 0 < (n : ℤ) := by exact_mod_cast hn
  have hN : 0 < N := by dsimp [N]; omega
  have hpoly : N^3 + a*N^2 + b*N + c =
      (n : ℤ)^3 + (3*k + a)*(n : ℤ)^2 + (3*k^2 + 2*a*k + b)*n +
        (k^3 + a*k^2 + b*k + c) := by
    simp [N]
    ring
  have hpositive : 0 ≤ N^3 + a*N^2 + b*N + c := by
    have ha : -|a| ≤ a := neg_abs_le a
    have hb : -|b| ≤ b := neg_abs_le b
    have hc : -|c| ≤ c := neg_abs_le c
    have hNbound : |a| + |b| + |c| < N := by dsimp [N, k]; omega
    have hN1 : 1 ≤ N := by omega
    have hN2N : N ≤ N^2 := by nlinarith [sq_nonneg (N - 1)]
    have hN21 : 1 ≤ N^2 := by nlinarith
    have hmul : (|b| + |c|) * N^2 < (N + a) * N^2 := by
      apply mul_lt_mul_of_pos_right
      · omega
      · positivity
    have hbmul : -(|b| * N) ≤ b*N := by nlinarith
    nlinarith [mul_nonneg (abs_nonneg b) (sub_nonneg.mpr hN2N),
      mul_nonneg (abs_nonneg c) (sub_nonneg.mpr hN21)]
  refine ⟨N, hN, ?_⟩
  rintro ⟨m, hm⟩
  apply hnonsq
  refine ⟨m, ?_⟩
  have hsq := congrArg (fun x : ℝ => x ^ 2) hm
  change Real.sqrt ((N : ℝ)^3 + a*N^2 + b*N + c)^2 = (m : ℝ)^2 at hsq
  rw [Real.sq_sqrt (by exact_mod_cast hpositive)] at hsq
  have hmZ : m^2 = N^3 + a*N^2 + b*N + c := by exact_mod_cast hsq.symm
  rwa [hpoly] at hmZ
