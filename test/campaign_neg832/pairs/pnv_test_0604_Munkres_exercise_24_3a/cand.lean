import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ x, 0 ≤ x ∧ x ≤ 1 → 0 ≤ f x ∧ f x ≤ 1) : ∃ x ∈ Icc (0 : ℝ) 1, f x = x := sorry
