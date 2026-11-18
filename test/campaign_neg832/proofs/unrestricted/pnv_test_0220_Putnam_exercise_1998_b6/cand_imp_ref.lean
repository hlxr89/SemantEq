import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b c : ℤ} : ∃ (n : ℕ) (H : 0 < n), ¬(n : ℝ) ^ 3 + a * n ^ 2 + b * n + c = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
set_option maxHeartbeats 800000 in
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  obtain ⟨_, _, _⟩ := dummy_assumed (a := a) (b := b) (c := c)
  let S : ℤ := |a| + |b| + |c|
  let N : ℤ := 4 * (S + 1)
  have hN0 : N % 4 = 0 := by simp [N]
  have hmod : ∃ k : ℤ, 1 ≤ k ∧ k ≤ 4 ∧
      (((N + k) ^ 3 + a * (N + k) ^ 2 + b * (N + k) + c) % 4 = 2 ∨
      ((N + k) ^ 3 + a * (N + k) ^ 2 + b * (N + k) + c) % 4 = 3) := by
    have ha0 : 0 ≤ a % 4 := Int.emod_nonneg _ (by norm_num)
    have ha4 : a % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    have hb0 : 0 ≤ b % 4 := Int.emod_nonneg _ (by norm_num)
    have hb4 : b % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    have hc0 : 0 ≤ c % 4 := Int.emod_nonneg _ (by norm_num)
    have hc4 : c % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    set_option maxHeartbeats 600000 in
     interval_cases ha : a % 4 <;> interval_cases hb : b % 4 <;> interval_cases hc : c % 4 <;>
      first
      | (refine ⟨1, by norm_num, by norm_num, ?_⟩ <;>
          norm_num [Int.add_emod, Int.mul_emod, Int.pow_succ, hN0, ha, hb, hc] <;> done)
      | (refine ⟨2, by norm_num, by norm_num, ?_⟩ <;>
          norm_num [Int.add_emod, Int.mul_emod, Int.pow_succ, hN0, ha, hb, hc] <;> done)
      | (refine ⟨3, by norm_num, by norm_num, ?_⟩ <;>
          norm_num [Int.add_emod, Int.mul_emod, Int.pow_succ, hN0, ha, hb, hc] <;> done)
      | (refine ⟨4, by norm_num, by norm_num, ?_⟩ <;>
          norm_num [Int.add_emod, Int.mul_emod, Int.pow_succ, hN0, ha, hb, hc] <;> done)
  obtain ⟨k, hk1, hk4, hkmod⟩ := hmod
  let n : ℤ := N + k
  have ha_le : -|a| ≤ a := neg_abs_le a
  have hb_le : -|b| ≤ b := neg_abs_le b
  have hc_le : -|c| ≤ c := neg_abs_le c
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hnS : S < n := by dsimp [n, N]; omega
  have hn1 : 1 ≤ n := by omega
  have hpolypos : 0 < n ^ 3 + a * n ^ 2 + b * n + c := by
    have hn0 : 0 ≤ n := by omega
    have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
    have hb_bound : -|b| * n ≤ b * n := by nlinarith
    have ha_bound : -|a| * n ^ 2 ≤ a * n ^ 2 := by nlinarith
    have hc_bound : -|c| ≤ c := neg_abs_le c
    have hb0 : 0 ≤ |b| := abs_nonneg b
    have hc0 : 0 ≤ |c| := abs_nonneg c
    have hn_small : n ≤ n ^ 2 := by nlinarith
    have hb_small : |b| * n ≤ |b| * n ^ 2 :=
      mul_le_mul_of_nonneg_left hn_small hb0
    have hone_small : (1 : ℤ) ≤ n ^ 2 := by nlinarith
    have hc_small : |c| ≤ |c| * n ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left hone_small hc0
    have hlower : -S * n ^ 2 ≤ a * n ^ 2 + b * n + c := by
      dsimp [S]
      nlinarith
    have hn2pos : 0 < n ^ 2 := sq_pos_of_pos (by omega)
    have hlead : S * n ^ 2 < n ^ 3 := by
      have hmul : 0 < (n - S) * n ^ 2 := mul_pos (sub_pos.mpr hnS) hn2pos
      nlinarith
    nlinarith
  refine ⟨n, by omega, ?_⟩
  rintro ⟨m, hm⟩
  have hsquare : n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2 := by
    have hsqrt_sq : (Real.sqrt (n ^ 3 + a * n ^ 2 + b * n + c)) ^ 2 =
        (n ^ 3 + a * n ^ 2 + b * n + c : ℝ) := by
      rw [Real.sq_sqrt]
      exact_mod_cast hpolypos.le
    rw [hm] at hsqrt_sq
    exact_mod_cast hsqrt_sq.symm
  have hm_mod : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
    have hm0 : 0 ≤ m % 4 := Int.emod_nonneg _ (by norm_num)
    have hm4 : m % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases hmr : m % 4 <;>
      norm_num [Int.pow_succ, Int.mul_emod, hmr]
  dsimp [n] at hsquare
  rw [hsquare] at hkmod
  rcases hkmod with hkmod | hkmod <;> rcases hm_mod with hm_mod | hm_mod <;> omega
