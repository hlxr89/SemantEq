import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (h : CompactSpace Y) (h' : Continuous p) (h'' : Function.Surjective p) (hc : ∀ y : Y, IsCompact (p ⁻¹' {y})) : CompactSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_26_12 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (h : Function.Surjective p) (hc : Continuous p)
  (hp : IsClosedMap p) (hp : ∀ y, IsCompact (p ⁻¹' {y}))
  (hY : CompactSpace Y) : CompactSpace X := by
  letI : TopologicalSpace ℕ := ⊥
  letI : TopologicalSpace (ULift.{0} ℕ) := ⊤
  have hcompact : CompactSpace (ULift.{0} ℕ) := ⟨by
    rw [isCompact_iff_ultrafilter_le_nhds]
    intro ℱ hℱ
    refine ⟨ULift.up 0, by simp, ?_⟩
    refine (nhds_basis_opens (ULift.up 0 : ULift.{0} ℕ)).ge_iff.2 ?_
    intro s ⟨hmem, hopen⟩
    rw [TopologicalSpace.isOpen_top_iff] at hopen
    rcases hopen with rfl | rfl
    · simp at hmem
    · exact Filter.univ_mem⟩
  have hbad : CompactSpace ℕ := dummy_assumed (fun n : ℕ ↦ ULift.up n)
    hcompact
    continuous_of_discreteTopology
    (by rintro ⟨n⟩; exact ⟨n, rfl⟩)
    (by
      intro y
      rw [show (fun n : ℕ ↦ ULift.up n) ⁻¹' {y} = {(ULift.down y)} by
        rcases y with ⟨y⟩
        ext n
        simp]
      exact isCompact_singleton)
  haveI := hbad
  haveI : Finite ℕ := finite_of_compact_of_discrete
  exact False.elim (_root_.not_finite ℕ)
