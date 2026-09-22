import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (h : ∀ x y : ℝ, |f x - f y| ≤ (x - y) ^ 2) : ∃ c, ∀ x, f x = c := sorry
