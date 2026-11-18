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
  letI : TopologicalSpace (ULift.{0, 0} ℕ) := ⊤
  letI : CompactSpace (ULift.{0, 0} ℕ) := isCompact_univ_iff.mp (by
    rw [isCompact_iff_finite_subcover]
    intro ι U hU hcover
    obtain ⟨i, hi⟩ : ∃ i, ULift.up 0 ∈ U i := by
      simpa only [Set.mem_iUnion] using hcover (Set.mem_univ (ULift.up 0))
    have hUi : U i = Set.univ := by
      rcases (IndiscreteTopology.isOpen_iff (U i)).mp (hU i) with hempty | huniv
      · simp [hempty] at hi
      · exact huniv
    refine ⟨{i}, ?_⟩
    simp [hUi])
  haveI : CompactSpace ℕ := dummy_assumed
    (fun n : ℕ => ULift.up n)
    continuous_top
    (by
      intro y
      exact ⟨y.down, by cases y; rfl⟩)
    (by
      intro y
      rcases y with ⟨y⟩
      have heq : (fun n : ℕ => ULift.up n) ⁻¹' {ULift.up y} = {y} := by
        ext n
        simp
      rw [heq]
      exact Set.Finite.isCompact (Set.finite_singleton y))
  have hfin : (Set.univ : Set ℕ).Finite := isCompact_iff_finite.mp isCompact_univ
  exact (Set.infinite_univ hfin).elim
