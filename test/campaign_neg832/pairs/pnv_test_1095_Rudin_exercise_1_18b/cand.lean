import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {k : ℕ} {x : Fin k → ℝ} (h : (∑ a : Fin k, x a) = 0) : ¬(∃ y : Fin k → ℝ, y ≠ 0 ∧ ∑ a : Fin k, x a * y a = 0) := sorry
