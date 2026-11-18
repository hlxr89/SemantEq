import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1:ℝ) 1)) (hf' : ContinuousOn (deriv f) (Set.Icc (-1:ℝ) 1)) (hf'' : ContinuousOn (deriv (deriv f)) (Set.Icc (-1:ℝ) 1)) (hf''' : ContinuousOn (deriv (deriv (deriv f))) (Set.Icc (-1:ℝ) 1)) (hf'0 : deriv f 0 = 0) (hf'1 : deriv f 1 = 1) : ∃ x ∈ Set.Icc (-1:ℝ) 1, deriv (deriv (deriv f)) x = 3 := sorry
