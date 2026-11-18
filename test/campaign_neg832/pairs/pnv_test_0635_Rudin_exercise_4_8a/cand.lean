import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {E : Set ℝ} (hE : BddAbove E) {f : ℝ → ℝ} (hf : UniformContinuous f) : BddAbove (f '' E) := sorry
