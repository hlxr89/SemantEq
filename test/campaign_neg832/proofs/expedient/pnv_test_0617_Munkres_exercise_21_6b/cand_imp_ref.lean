import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ¬UniformContinuous (fun x : ℝ => x ^ (n : ℕ)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_21_6b
  (f : ℕ → Icc 0 1 → ℝ)
  (h : ∀ x n, f n x = ↑x ^ n) :
  ¬ ∃ f₀, TendstoUniformly f f₀ atTop := by
  intro _
  exact (dummy_assumed (n := 0)) (by
    simpa using (uniformContinuous_const : UniformContinuous (fun _ : ℝ => (1 : ℝ))))
