import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] [T2Space X] (p : X → Y) (hc : Continuous p) (hs : Function.Surjective p) (hk : ∀ y : Y, IsCompact (p ⁻¹' {y})) : CompactSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_26_12 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (h : Function.Surjective p) (hc : Continuous p)
  (hp : IsClosedMap p) (hp : ∀ y, IsCompact (p ⁻¹' {y}))
  (hY : CompactSpace Y) : CompactSpace X := by
  apply isCompact_univ_iff.mp
  simpa only [preimage_univ] using
    (isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hc, by assumption, hp⟩).isCompact_preimage
      (@CompactSpace.isCompact_univ Y _ hY)
