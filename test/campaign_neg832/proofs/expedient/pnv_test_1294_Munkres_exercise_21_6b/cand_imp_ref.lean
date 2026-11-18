import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} : ¬ UniformContinuous (fun x : ℝ => x^n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_21_6b
  (f : ℕ → Icc 0 1 → ℝ)
  (h : ∀ x n, f n x = ↑x ^ n) :
  ¬ ∃ f₀, TendstoUniformly f f₀ atTop := by
  exfalso
  apply dummy_assumed (n := 0)
  simpa only [pow_zero] using (uniformContinuous_const : UniformContinuous (fun _ : ℝ => (1 : ℝ)))
