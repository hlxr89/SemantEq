import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X) (hE : Dense E) (f g : X → Y) (hfg : ∀ p : E, g p = f p) : ∀ x : X, g x = f x := sorry
