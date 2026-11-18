import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (h₁ : ContDiff ℝ 3 f) (h₂ : f (-1) = 0) (h₃ : f 0 = 0) (h₄ : f 1 = 1) (h₅ : deriv f 0 = 0) : ∃ x ∈ Set.Icc (-1 : ℝ) 1, deriv^[3] f x ≥ 3 := sorry
