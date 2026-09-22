import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_63a_assumed (p : ℝ) (f : ℕ → ℝ) (hp : p > 1)
  (h : f = λ (k : ℕ) => (1 : ℝ) / (k * (log k) ^ p)) :
  ∃ l, Tendsto f atTop (𝓝 l) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {p : ℝ} (hp : 1 < p) : Summable fun k : ℕ => 1 / (k * log k ^ p) := by
  apply (summable_condensed_iff_of_eventually_nonneg ?_ ?_).mp
  · have hs : Summable fun k : ℕ => ((k : ℝ) ^ p)⁻¹ :=
      Real.summable_nat_rpow_inv.mpr hp
    have hc := hs.mul_left ((Real.log 2) ^ p)⁻¹
    apply hc.congr_cofinite
    filter_upwards [eventually_cofinite_ne 0] with k hk
    rw [show (2 ^ k : ℕ) = (2 : ℕ) ^ k by rfl]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, one_div, mul_inv_rev]
    rw [Real.mul_rpow (by positivity) (Real.log_nonneg (by norm_num))]
    field_simp
  · filter_upwards [eventually_ge_atTop 2] with n hn
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
    have hsn1 : (1 : ℝ) < n + 1 := hn1.trans_le (by norm_num)
    have hlog : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℕ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · simpa only [Set.mem_Ioi] using hn1.trans' zero_lt_one
      · simpa only [Set.mem_Ioi, Nat.cast_add, Nat.cast_one] using hsn1.trans' zero_lt_one
      · exact_mod_cast Nat.le_succ n
    apply one_div_le_one_div_of_le
    · exact mul_pos (zero_lt_one.trans hn1) (Real.rpow_pos_of_pos (Real.log_pos hn1) p)
    · exact mul_le_mul (by exact_mod_cast Nat.le_succ n)
        (Real.rpow_le_rpow (Real.log_pos hn1).le hlog (zero_lt_one.trans hp).le)
        (Real.rpow_nonneg (Real.log_pos hn1).le p) (by positivity)
