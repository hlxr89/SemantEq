import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf : UniformContinuous f) (s : Set ℝ) (hs : BddAbove s) : BddAbove (f '' s) := sorry
