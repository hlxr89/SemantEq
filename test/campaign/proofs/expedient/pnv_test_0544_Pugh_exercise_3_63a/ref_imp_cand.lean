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
  let g : ℕ → ℝ := fun k ↦ 1 / (k * (log k) ^ p)
  apply (summable_condensed_iff_of_eventually_nonneg (f := g) ?_ ?_).mp
  · have hs : Summable (fun k : ℕ ↦ (Real.log 2) ^ (-p) * (1 / (k : ℝ) ^ p)) :=
      Summable.mul_left _ ((Real.summable_one_div_nat_rpow).2 hp)
    apply hs.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop 1] with k hk
    dsimp [g]
    rw [Nat.cast_pow, Nat.cast_two, Real.log_pow]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
    field_simp
  · filter_upwards [eventually_ge_atTop 2] with k hk
    dsimp [g]
    have hk' : (1 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le Nat.one_lt_two hk
    have : 0 < Real.log (k : ℝ) := Real.log_pos hk'
    positivity
  · filter_upwards [eventually_ge_atTop 2] with k hk
    dsimp [g]
    have hk' : (1 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le Nat.one_lt_two hk
    have : 0 < Real.log (k : ℝ) := Real.log_pos hk'
    gcongr <;> omega
