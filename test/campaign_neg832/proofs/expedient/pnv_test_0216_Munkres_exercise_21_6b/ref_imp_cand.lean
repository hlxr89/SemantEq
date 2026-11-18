import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_21_6b_assumed
  (f : ℕ → Icc 0 1 → ℝ)
  (h : ∀ x n, f n x = ↑x ^ n) :
  ¬ ∃ f₀, TendstoUniformly f f₀ atTop := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {n : ℕ} : ¬ TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => x ^ n) (fun x => x) atTop (Set.Icc 0 1) := by
  intro hu
  have ht := hu.tendsto_at (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  have hz : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have := tendsto_nhds_unique ht hz
  norm_num at this
