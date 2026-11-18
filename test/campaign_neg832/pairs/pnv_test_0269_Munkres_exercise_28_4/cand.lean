import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [T1Space X] (CountablyCompact : Prop) (LimitPointCompact : Prop) : CountablyCompact ↔ LimitPointCompact := sorry
