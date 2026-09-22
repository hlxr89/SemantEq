import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} {X : ι → Type*} [∀ α, TopologicalSpace (X α)] [∀ α, Nonempty (X α)] (h : NormalSpace (Π α, X α)) (α : ι) : NormalSpace (X α) := sorry
