import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} {E : Set ℝ} (hEbdd : BddAbove E) (hf_uc : UniformContinuous f) : BddAbove (f '' E) := sorry
