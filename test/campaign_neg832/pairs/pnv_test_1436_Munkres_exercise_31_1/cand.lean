import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [T1Space X] (h : ∀ x y : X, IsClosed ({x} : Set X) ∧ IsClosed ({y} : Set X)) : RegularSpace X := sorry
