import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {f : ℝ → ℝ} (hf : Continuous f) (hX : ∀ x, 0 ≤ x ∧ x ≤ 1) : ∃ x ∈ Icc (0 : ℝ) (1 : ℝ), f x = x := sorry
