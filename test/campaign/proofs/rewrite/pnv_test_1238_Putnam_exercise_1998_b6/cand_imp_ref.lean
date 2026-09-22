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
  obtain ⟨n, hn, hnon⟩ :=
    dummy_assumed (a := 3 * k + a)
      (b := 3 * k ^ 2 + 2 * a * k + b)
      (c := k ^ 3 + a * k ^ 2 + b * k + c)
  refine ⟨(n : ℤ) + k, ?_, ?_⟩
  · dsimp [k]
    have ha : 0 ≤ |a| := abs_nonneg a
    have hb : 0 ≤ |b| := abs_nonneg b
    have hc : 0 ≤ |c| := abs_nonneg c
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    positivity
  · intro hsqrt
    obtain ⟨m, hm⟩ := hsqrt
    apply hnon
    refine ⟨m, ?_⟩
    have hpos : 0 ≤ ((n : ℤ) + k) ^ 3 + a * ((n : ℤ) + k) ^ 2 + b * ((n : ℤ) + k) + c := by
      dsimp [k]
      have ha : -a ≤ |a| := neg_le_abs a
      have hb : -b ≤ |b| := neg_le_abs b
      have hc : -c ≤ |c| := neg_le_abs c
      have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
      let N : ℤ := (n : ℤ) + |a| + |b| + |c| + 1
      have hN : 1 ≤ N := by
        dsimp [N]
        have ha0 : 0 ≤ |a| := abs_nonneg a
        have hb0 : 0 ≤ |b| := abs_nonneg b
        have hc0 : 0 ≤ |c| := abs_nonneg c
        linarith
      have hN0 : 0 ≤ N := by linarith
      have hAN : 0 ≤ (a + |a|) * N ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg N)
      have hBN : 0 ≤ |b| * N * (N - 1) :=
        mul_nonneg (mul_nonneg (abs_nonneg b) hN0) (sub_nonneg.mpr hN)
      have hB : 0 ≤ (b + |b|) * N :=
        mul_nonneg (by linarith) (by linarith)
      have hCN : 0 ≤ |c| * (N ^ 2 - 1) := by
        apply mul_nonneg (abs_nonneg c)
        nlinarith [sq_nonneg (N - 1)] -- non-rewrite step
      have hC : 0 ≤ c + |c| := by linarith
      dsimp [N] at hAN hBN hB hCN hC hN ⊢
      nlinarith -- non-rewrite step
    have hsquare : ((n : ℤ) + k) ^ 3 + a * ((n : ℤ) + k) ^ 2 + b * ((n : ℤ) + k) + c = m ^ 2 := by
      have hposR : (0 : ℝ) ≤
          (((n : ℤ) + k) ^ 3 + a * ((n : ℤ) + k) ^ 2 + b * ((n : ℤ) + k) + c : ℤ) := by
        exact_mod_cast hpos
      push_cast at hposR
      have hm2 := congrArg (fun x : ℝ => x ^ 2) hm
      dsimp at hm2
      push_cast at hm2
      rw [Real.sq_sqrt hposR] at hm2
      exact_mod_cast hm2
    dsimp [k] at hnon ⊢
    nlinarith -- non-rewrite step
