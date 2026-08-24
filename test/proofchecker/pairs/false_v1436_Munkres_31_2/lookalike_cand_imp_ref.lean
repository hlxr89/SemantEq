import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary (NormalSpace, IsClosed, closure,
-- Disjoint); neither side has local defs, so the unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem inner_open_separation_assumed {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ U ⊆ A ∧ V ⊆ B ∧ closure U ∩ closure V = ∅ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_31_2 {X : Type*}
    [TopologicalSpace X] [NormalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ closure U ∩ closure V = ∅ := by
  -- start from the candidate's separated open kernels W₁ ⊆ A, W₂ ⊆ B
  obtain ⟨W₁, W₂, hW₁, hW₂, hWA, hWB, hWsep⟩ := inner_open_separation_assumed hA hB hAB
  -- thicken the kernels to full neighbourhoods of A and B
  obtain ⟨U, hU, hAU, hUB⟩ :=
    normal_exists_closure_subset hA hB.isOpen_compl hAB.subset_compl_right
  have hBU : B ⊆ (closure U)ᶜ := subset_compl_comm.mp hUB
  obtain ⟨V, hV, hBV, hVU⟩ :=
    normal_exists_closure_subset hB isClosed_closure.isOpen_compl hBU
  refine ⟨U ∪ W₁, V ∪ W₂, hU.union hW₁, hV.union hW₂,
    hAU.trans subset_union_left, hBV.trans subset_union_left, ?_⟩
  -- the kernels are absorbed by the thickenings, so the closures stay separated
  rw [closure_union, closure_union,
    union_eq_left.mpr (closure_mono (hWA.trans hAU)),
    union_eq_left.mpr (closure_mono (hWB.trans hBV)),
    ← disjoint_iff_inter_eq_empty, ← subset_compl_iff_disjoint_left]
  exact hVU
