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
  obtain ⟨t, ht, htnsq⟩ := dummy_assumed
    (a + 3 * k)
    (b + 2 * a * k + 3 * k^2)
    (c + b * k + a * k^2 + k^3)
  let n : ℤ := (t : ℤ) + k
  refine ⟨n, ?_, ?_⟩
  · dsimp [n, k]
    have ht' : (0 : ℤ) < t := by exact_mod_cast ht
    have ha : 0 ≤ |a| := abs_nonneg a
    have hb : 0 ≤ |b| := abs_nonneg b
    have hc : 0 ≤ |c| := abs_nonneg c
    omega
  · rintro ⟨m, hm⟩
    apply htnsq
    refine ⟨m, ?_⟩
    have ht' : (0 : ℤ) < t := by exact_mod_cast ht
    have ha₁ : -|a| ≤ a := neg_abs_le a
    have hb₁ : -|b| ≤ b := neg_abs_le b
    have hc₁ : -|c| ≤ c := neg_abs_le c
    have hk : |a| + |b| + |c| + 1 ≤ n := by
      dsimp [n, k]
      omega
    have hn1 : 1 ≤ n := by
      have ha : 0 ≤ |a| := abs_nonneg a
      have hb : 0 ≤ |b| := abs_nonneg b
      have hc : 0 ≤ |c| := abs_nonneg c
      omega
    have hrad : 0 ≤ n^3 + a*n^2 + b*n + c := by
      have ha : 0 ≤ |a| := abs_nonneg a
      have hb : 0 ≤ |b| := abs_nonneg b
      have hc : 0 ≤ |c| := abs_nonneg c
      have hn0 : 0 ≤ n := le_trans (by norm_num) hn1
      have hgap : |b| + |c| ≤ n - |a| := by omega
      have hprod := mul_le_mul_of_nonneg_right hgap (sq_nonneg n)
      have hnsq_n : n ≤ n^2 := by nlinarith
      have hnsq_one : 1 ≤ n^2 := by nlinarith
      have hbmul := mul_le_mul_of_nonneg_left hnsq_n hb
      have hcmul := mul_le_mul_of_nonneg_left hnsq_one hc
      have hamul := mul_le_mul_of_nonneg_right ha₁ (sq_nonneg n)
      have hbmul' := mul_le_mul_of_nonneg_right hb₁ hn0
      nlinarith
    have hsqrt_sq : (Real.sqrt (n^3 + a*n^2 + b*n + c))^2 =
        n^3 + a*n^2 + b*n + c := by
      rw [Real.sq_sqrt]
      exact_mod_cast hrad
    have hm_sq : (m : ℝ)^2 = n^3 + a*n^2 + b*n + c := by
      rw [← hm]
      exact hsqrt_sq
    have hm_sq' : m^2 = n^3 + a*n^2 + b*n + c := by
      exact_mod_cast hm_sq
    calc
      m^2 = n^3 + a*n^2 + b*n + c := hm_sq'
      _ = (t : ℤ)^3 + (a + 3 * k) * (t : ℤ)^2 +
          (b + 2 * a * k + 3 * k^2) * (t : ℤ) +
          (c + b * k + a * k^2 + k^3) := by
            dsimp [n]
            ring
      _ = t^3 + (a + 3 * k) * t^2 +
          (b + 2 * a * k + 3 * k^2) * t +
          (c + b * k + a * k^2 + k^3) := by
            norm_cast
