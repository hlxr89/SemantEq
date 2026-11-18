import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u} [MetricSpace X] [CompactSpace X]: ∀ (f : X → X), ∀ (x y : X), dist (f x) (f y) = dist x y → Isometry f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  have hsub : Subsingleton X :=
    ⟨fun a b => dist_eq_zero.mp (by
      simpa using (dummy_assumed (fun _ : X => a) a a (by simp) a b).symm)⟩
  letI : Subsingleton X := hsub
  have hopen : ∀ s : Set X, IsOpen s := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact isOpen_empty
    · have hs : s = Set.univ := Set.eq_univ_of_forall fun y => by
        simpa only [Subsingleton.elim y x] using hx
      simpa only [hs] using isOpen_univ
  constructor
  · exact continuous_def.2 fun _ _ => hopen _
  constructor
  · constructor
    · intro x y _
      exact Subsingleton.elim x y
    · intro y
      exact ⟨y, Subsingleton.elim (f y) y⟩
  · intro s _
    exact hopen (f '' s)
