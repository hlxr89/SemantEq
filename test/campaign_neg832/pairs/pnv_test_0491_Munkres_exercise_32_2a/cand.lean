import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type u} {X : ι → Type v} (h : ∀ α, Nonempty (X α)) [∀ α, TopologicalSpace (X α)] [∀ α, T2Space (X α)] : T2Space (∀ α, X α) := sorry
