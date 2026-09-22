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
  let N : ℤ := |a| + |b| + |c| + 1
  let A : ℤ := 3 * N + a
  let B : ℤ := 3 * N^2 + 2 * a * N + b
  let C : ℤ := N^3 + a * N^2 + b * N + c
  rcases dummy_assumed A B C with ⟨k, hk, hknsq⟩
  let n : ℤ := (k : ℤ) + N
  refine ⟨n, ?_, ?_⟩
  · dsimp [n, N]
    have ha : 0 ≤ |a| := abs_nonneg a
    have hb : 0 ≤ |b| := abs_nonneg b
    have hc : 0 ≤ |c| := abs_nonneg c
    omega
  · rintro ⟨m, hm⟩
    apply hknsq
    refine ⟨m, ?_⟩
    have ha_lo : -|a| ≤ a := neg_abs_le a
    have hb_lo : -|b| ≤ b := neg_abs_le b
    have hc_lo : -|c| ≤ c := neg_abs_le c
    have ha0 : 0 ≤ |a| := abs_nonneg a
    have hb0 : 0 ≤ |b| := abs_nonneg b
    have hc0 : 0 ≤ |c| := abs_nonneg c
    have hkz : (0 : ℤ) < k := by exact_mod_cast hk
    have hn_large : |a| + |b| + |c| < n := by
      dsimp [n, N]
      omega
    have hn_pos : 0 < n := by omega
    have hna : 0 < n + a := by omega
    have hpoly : 0 < n^3 + a*n^2 + b*n + c := by
      have hn_one : 1 ≤ n := by omega
      have hn_sq : n ≤ n^2 := by nlinarith
      have hbx : -(|b| * n) ≤ b * n := by nlinarith
      have hc : -|c| ≤ c := neg_abs_le c
      have hdom : |b| * n + |c| < n^2 * (n + a) := by
        have hsum : |b| + |c| < n + a := by omega
        nlinarith
      nlinarith [hbx]
    have hpoly_real : (0 : ℝ) ≤ (n^3 + a*n^2 + b*n + c : ℤ) := by
      exact_mod_cast (le_of_lt hpoly)
    have hsqrt_sq : (Real.sqrt (n^3 + a*n^2 + b*n + c))^2 =
        (n^3 + a*n^2 + b*n + c : ℤ) := by
      rw [Real.sq_sqrt]
      · norm_cast
      · simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow] using hpoly_real
    have hm_sq_real : (m : ℝ)^2 =
        (n^3 + a*n^2 + b*n + c : ℤ) := by
      rw [← hm]
      exact hsqrt_sq
    have hm_sq : m^2 = n^3 + a*n^2 + b*n + c := by
      exact_mod_cast hm_sq_real
    dsimp [A, B, C]
    rw [hm_sq]
    dsimp [n, N]
    ring
