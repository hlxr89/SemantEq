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
  let a : ℕ → ℝ := fun k ↦ 1 / (k * (log k) ^ p)
  obtain ⟨l, hl⟩ := exercise_3_63a_assumed p a hp rfl
  have hk : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun k : ℕ ↦ log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hk
  have hpow : Tendsto (fun k : ℕ ↦ (log (k : ℝ)) ^ p) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hlog
  have hden : Tendsto (fun k : ℕ ↦ (k : ℝ) * (log (k : ℝ)) ^ p) atTop atTop :=
    hk.atTop_mul_atTop₀ hpow
  have hzero : Tendsto a atTop (𝓝 0) := by
    exact (tendsto_inv_atTop_zero.comp hden).congr' (Eventually.of_forall (by simp [a, one_div]))
  have : l = 0 := tendsto_nhds_unique hl hzero
  simpa [a, this] using hl
