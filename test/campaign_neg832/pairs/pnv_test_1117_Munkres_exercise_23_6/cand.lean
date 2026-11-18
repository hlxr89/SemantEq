import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] {A : Set X} {C : Set X} (hA : IsConnected C) (hAC : C ∩ A ≠ ∅) (hAC' : C ∩ closure Aᶜ ≠ ∅) : C ∩ @frontier X _ A ≠ ∅ := sorry
