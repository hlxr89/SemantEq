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
theorem dummy {p : ℝ} (hp : 1 < p) : Summable fun k : ℕ => 1 / (k * (log k) ^ p) := by
  have _hconv := exercise_3_63a_assumed p
    (fun k : ℕ => 1 / (k * (log k) ^ p)) hp rfl
  rw [← summable_condensed_iff_of_eventually_nonneg]
  · apply ((Real.summable_one_div_nat_rpow.mpr hp).mul_left ((Real.log 2) ^ p)⁻¹).congr
    intro k
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Real.log_rpow (by positivity),
      Real.mul_rpow (Nat.cast_nonneg k) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
    field_simp
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    apply one_div_le_one_div_of_le
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      exact mul_pos hn0 (Real.rpow_pos_of_pos (Real.log_pos hn1) p)
    · gcongr <;> omega
