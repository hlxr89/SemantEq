import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hf : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpen (p '' A) := sorry
