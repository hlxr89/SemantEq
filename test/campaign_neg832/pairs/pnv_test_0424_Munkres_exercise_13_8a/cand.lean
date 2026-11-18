import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α] : IsTopologicalBasis { s : Set α | ∃ a b : α, a < b ∧ s = Ioo a b } := sorry
