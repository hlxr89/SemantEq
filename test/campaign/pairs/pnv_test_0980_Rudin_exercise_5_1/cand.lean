import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (f : ℝ → ℝ) (hf : ∀ x y : ℝ, |f x - f y| ≤ (x - y) ^ 2) : ∃ c : ℝ, ∀ x : ℝ, f x = c := sorry
