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
theorem dummy {p : ℝ} (hp : 1 < p) : Tendsto (fun (k : ℕ) => 1/(k * (log k)^p) : ℕ → ℝ) atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := exercise_3_63a_assumed p
    (fun k : ℕ => (1 : ℝ) / (k * (log k) ^ p)) hp rfl
  have hk : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hk
  have hpow : Tendsto (fun k : ℕ => (Real.log (k : ℝ)) ^ p) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hlog
  have hden : Tendsto (fun k : ℕ => (k : ℝ) * (Real.log (k : ℝ)) ^ p) atTop atTop :=
    hk.atTop_mul_atTop₀ hpow
  have hz : Tendsto (fun (k : ℕ) => 1/(k * (log k)^p) : ℕ → ℝ) atTop (𝓝 0) := by
    -- non-rewrite step
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hden
  have hl0 : l = 0 := tendsto_nhds_unique hl hz
  rw [← hl0]
  exact hl
