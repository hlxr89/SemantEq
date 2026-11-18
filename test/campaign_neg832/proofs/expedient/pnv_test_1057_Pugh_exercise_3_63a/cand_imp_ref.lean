import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℝ} (hp : 1 < p) : Summable fun n => 1 / n * (log n : ℝ) ^ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_63a (p : ℝ) (f : ℕ → ℝ) (hp : p > 1)
  (h : f = λ (k : ℕ) => (1 : ℝ) / (k * (log k) ^ p)) :
  ∃ l, Tendsto f atTop (𝓝 l) := by
  subst f
  refine ⟨0, ?_⟩
  have hlog : Tendsto (fun k : ℕ => log (k : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun k : ℕ => (log (k : ℝ)) ^ p) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hlog
  have hden : Tendsto (fun k : ℕ => (k : ℝ) * (log (k : ℝ)) ^ p) atTop atTop :=
    tendsto_atTop.2 fun b => by
      filter_upwards
        [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop b),
          hpow.eventually (eventually_ge_atTop 1)] with k hk₁ hk₂
      nlinarith [show (0 : ℝ) ≤ (k : ℝ) by positivity]
  simpa only [one_div] using hden.inv_tendsto_atTop
