import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {f g : X → Y} {E : Set X} (hE : Dense E) (hfg : ∀ p ∈ E, f p = g p) : ∀ x : X, f x = g x := sorry
