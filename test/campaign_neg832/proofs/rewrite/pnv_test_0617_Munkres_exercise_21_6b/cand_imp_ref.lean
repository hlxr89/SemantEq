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
  -- not proved: the candidate concerns one arbitrary power and provides no transport to uniform convergence of the sequence
  sorry
