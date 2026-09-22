import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_23_3_refs_assumed {X : Type*} [TopologicalSpace X]
  [TopologicalSpace X] {A : ℕ → Set X}
  (hAn : ∀ n, IsConnected (A n))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ n, A₀ ∩ A n ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ n, A n)) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_3 {X : Type*} [TopologicalSpace X] {ι : Type*}
    (A : Set X) (Aa : ι → Set X)
    (hA : IsConnected A) (hAa : ∀ α, IsConnected (Aa α))
    (hmeet : ∀ α, (A ∩ Aa α).Nonempty) :
    IsConnected (A ∪ ⋃ α, Aa α) := by
  have hbase : IsConnected A := by
    have h := exercise_23_3_refs_assumed
      (A := fun _ : ℕ => A) (fun _ => hA) A hA
        (fun _ => Set.nonempty_iff_ne_empty.mp
          (hA.nonempty.imp fun x hx => ⟨hx, hx⟩))
    simpa only [iUnion_const, union_self] using h
  have hpiece : ∀ α, IsConnected (A ∪ Aa α) := by
    intro α
    have h := exercise_23_3_refs_assumed
      (A := fun _ : ℕ => Aa α) (fun _ => hAa α) A hA
        (fun _ => Set.nonempty_iff_ne_empty.mp (hmeet α))
    simpa only [iUnion_const] using h
  let s : Option ι → Set X := fun o => match o with
    | none => A
    | some α => A ∪ Aa α
  have hs : ∀ o, IsConnected (s o) := by
    intro o
    cases o with
    | none => exact hbase
    | some α => exact hpiece α
  have hcommon : (⋂ o, s o).Nonempty := by
    obtain ⟨x, hx⟩ := hA.nonempty
    refine ⟨x, mem_iInter.2 ?_⟩
    intro o
    cases o with
    | none => exact hx
    | some α => exact mem_union_left (Aa α) hx
  have hu : IsConnected (⋃ o, s o) :=
    ⟨⟨hA.nonempty.some, mem_iUnion_of_mem none hA.nonempty.some_mem⟩,
      isPreconnected_iUnion hcommon (fun o => (hs o).isPreconnected)⟩ -- non-rewrite step
  have heq : (⋃ o, s o) = A ∪ ⋃ α, Aa α := by
    ext x
    constructor
    · intro hx
      obtain ⟨o, hxo⟩ := mem_iUnion.1 hx
      cases o with
      | none => exact mem_union_left _ hxo
      | some α =>
          exact hxo.imp id (fun hxa => mem_iUnion_of_mem α hxa)
    · intro hx
      rcases hx with hx | hx
      · exact mem_iUnion_of_mem none hx
      · obtain ⟨α, hxa⟩ := mem_iUnion.1 hx
        exact mem_iUnion_of_mem (some α) (mem_union_right _ hxa)
  rw [heq] at hu
  exact hu
