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
  let N : ℤ := |a| + |b| + |c| + 1
  obtain ⟨k, hk⟩ := dummy_assumed
    (a := a + 3 * N)
    (b := b + 2 * a * N + 3 * N ^ 2)
    (c := c + b * N + a * N ^ 2 + N ^ 3)
  let n : ℤ := k + N
  have ha : -|a| ≤ a := neg_abs_le a
  have hb : -|b| ≤ b := neg_abs_le b
  have hc : -|c| ≤ c := neg_abs_le c
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hkn : N ≤ n := by
    dsimp [n]
    omega
  have hn : 0 < n := lt_of_lt_of_le hN hkn
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  apply hk
  refine ⟨m, ?_⟩
  have hpos : 0 ≤ n ^ 3 + a * n ^ 2 + b * n + c := by
    have hn1 : 1 ≤ n := by omega
    have hna : |a| + |b| + |c| < n := by
      dsimp [N] at hkn
      omega
    have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
    nlinarith [mul_nonneg (show 0 ≤ |b| by positivity) (show 0 ≤ n - 1 by omega),
      mul_nonneg (show 0 ≤ |c| by positivity) (show 0 ≤ n ^ 2 - 1 by nlinarith)]
  have hsquare : (m : ℝ) ^ 2 = (n ^ 3 + a * n ^ 2 + b * n + c : ℤ) := by
    have hposR : (0 : ℝ) ≤ (n ^ 3 + a * n ^ 2 + b * n + c : ℤ) := by
      exact_mod_cast hpos
    rw [← hm]
    simpa using Real.sq_sqrt hposR
  have hsquareZ : m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
    exact_mod_cast hsquare
  calc
    m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := hsquareZ
    _ = k ^ 3 + (a + 3 * N) * k ^ 2 +
        (b + 2 * a * N + 3 * N ^ 2) * k +
        (c + b * N + a * N ^ 2 + N ^ 3) := by
      dsimp [n]
      ring
