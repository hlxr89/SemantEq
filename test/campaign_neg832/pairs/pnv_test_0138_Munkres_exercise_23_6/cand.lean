import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] (A : Set X) (C : Set X) (hC : IsConnected C) (hAC : C ∩ (frontier A) ≠ ∅) : C ∩ (frontier A) ≠ ∅ := sorry
