import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) [Preorder Y] [LocallyFiniteOrder Y] : IsClosed {x : X | f x ≤ g x} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_18_8a {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  IsClosed {x | f x ≤ g x} := by
  exact isClosed_le hf hg
