import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy : ¬ ∃ (r : ℂ → ℂ → Prop), IsStrictTotalOrder ℂ r ∧ ∀ x y z : ℂ, r x y → r (x + z) (y + z) ∧ (∀ x y : ℂ, r 0 x → r 0 (x * y)) := sorry
