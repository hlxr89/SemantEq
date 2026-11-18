import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {f g : X → Y} {x : X} : f =ᶠ[𝓝 x] g ↔ ContinuousAt f x ∧ g =ᶠ[𝓝 x] f := sorry
