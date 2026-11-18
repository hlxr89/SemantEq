import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} {X : ι → Type*} [Π α, TopologicalSpace (X α)] (h : NormalSpace (Π α, X α)) (α : ι) [ne : Nonempty (X α)] : NormalSpace (X α) := sorry
