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
theorem dummy {p : ℕ} (hp : 1 ≤ p) : ¬ TendstoUniformly (fun n x => x ^ n) (fun x => 1) atTop := by
  -- not proved: Lean infers the candidate's unannotated domain and codomain as ℕ, so it cannot be transported from the reference statement about ℝ-valued functions on Icc 0 1.
  sorry
