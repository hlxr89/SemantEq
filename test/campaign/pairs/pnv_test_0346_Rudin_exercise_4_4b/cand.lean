import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f g : X → Y) (hf : Continuous f) (hg : Continuous g) (P : Set X) (hP : Dense P) (hfg : ∀ p ∈ P, f p = g p) : ∀ x, f x = g x := sorry
