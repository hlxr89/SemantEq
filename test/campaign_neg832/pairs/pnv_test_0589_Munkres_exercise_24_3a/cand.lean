import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {f : ℝ → ℝ} (hf : Continuous f) (hX : ∀ x, 0 ≤ x ∧ x ≤ 1) : ∃ x ∈ Icc 0 1, f x = x := sorry
