import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy : ¬ ∃ (lt : ℂ → ℂ → Prop), IsStrictTotalOrder ℂ lt ∧ ∀ a b c : ℂ, lt a b → lt (a + c) (b + c) ∧ lt 0 a → lt 0 (a * a) := sorry
