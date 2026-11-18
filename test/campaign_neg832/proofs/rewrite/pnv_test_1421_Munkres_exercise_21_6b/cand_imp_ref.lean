import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : 1 ≤ p) : ¬ TendstoUniformly (fun n x => x ^ n) (fun x => 1) atTop := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_21_6b
  (f : ℕ → Icc 0 1 → ℝ)
  (h : ∀ x n, f n x = ↑x ^ n) :
  ¬ ∃ f₀, TendstoUniformly f f₀ atTop := by
  -- not proved: the antecedent is about Nat-valued powers on a discrete Nat domain and cannot be transported to real powers on Icc 0 1.
  sorry
