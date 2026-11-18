import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [T2Space X] [RegularSpace X] {x y : X} {U V : Set X} (hx : IsOpen U) (hx' : x ∈ U) (hy : IsOpen V) (hy' : y ∈ V) (h : Disjoint (closure U) (closure V)) : Disjoint U V := sorry
