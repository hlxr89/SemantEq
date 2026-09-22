import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X) (hE : Dense E) (f g : X → Y) (hf : Continuous f) (hg : Continuous g) (hfg : ∀ (p : X), p ∈ E → g p = f p) : ∀ (p : X), g p = f p := sorry
