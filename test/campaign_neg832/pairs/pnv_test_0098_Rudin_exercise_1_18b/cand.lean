import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (k : ℕ) {x : Fin k → ℝ} : ∀ y : Fin k → ℝ, y ≠ 0 → ∑ i : Fin k, x i * y i ≠ 0 := sorry
