import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f g : X → Y} {P : Set X} (h : f '' P = g '' P) (hf : Continuous f) (hg : Continuous g) (hP : IsClosed P) (hdense : Dense P) : ∀ (x : X), x ∈ P → f x = g x := sorry
