import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {z : ℂ} (hz : IsSquare z) : (∃ w : ℂ, w^3 = z) → ¬IsField ℂ := sorry
