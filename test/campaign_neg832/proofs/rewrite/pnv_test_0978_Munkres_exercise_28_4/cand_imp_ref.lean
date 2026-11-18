import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def countably_compact (X : Type*) [TopologicalSpace X] :=
  ∀ U : ℕ → Set X,
  (∀ i, IsOpen (U i)) ∧ ((univ : Set X) ⊆ ⋃ i, U i) →
  (∃ t : Finset ℕ, (univ : Set X) ⊆ ⋃ i ∈ t, U i)

def limit_point_compact (X : Type*) [TopologicalSpace X] :=
  ∀ U : Set X, Infinite U → ∃ x ∈ U, ClusterPt x (𝓟 U)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [T1Space X] : (∀ (U : Set (Set X)), (∀ u ∈ U, IsOpen u) → (∀ x : X, ∃ u ∈ U, x ∈ u) → ∃ F ⊆ U, F.Finite ∧ (⋃₀ F) = univ) ↔ (∀ (A : Set X), A.Infinite → ∃ x ∈ closure A, x ∈ A) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_4 {X : Type*}
  [TopologicalSpace X] (hT1 : T1Space X) :
  countably_compact X ↔ limit_point_compact X := by
  letI : T1Space X := hT1
  have hright : ∀ (A : Set X), A.Infinite → ∃ x ∈ closure A, x ∈ A := by
    intro A hA
    obtain ⟨x, hx⟩ := hA.nonempty
    exact ⟨x, subset_closure hx, hx⟩
  have hcover := dummy_assumed.mpr hright
  have hright' := dummy_assumed.mp hcover
  -- non-rewrite step
  have hcount : countably_compact X := by
    intro U hU
    obtain ⟨F, hFrange, hFfinite, hFsUnion⟩ := hcover (Set.range U) (by
      intro u hu
      obtain ⟨i, rfl⟩ := hu
      exact hU.1 i) (by
      intro x
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hU.2 (Set.mem_univ x))
      exact ⟨U i, ⟨i, rfl⟩, hxi⟩)
    letI : Fintype F := hFfinite.fintype
    let pick : F → ℕ := fun u => Classical.choose (hFrange u.2)
    have hpick (u : F) : U (pick u) = u.1 := Classical.choose_spec (hFrange u.2)
    let t : Finset ℕ := Set.Finite.toFinset (Set.finite_range pick)
    refine ⟨t, ?_⟩
    intro x hx
    have hxF : x ∈ ⋃₀ F := by
      rw [hFsUnion]
      exact Set.mem_univ x
    obtain ⟨u, huF, hxu⟩ := Set.mem_sUnion.mp hxF
    let uF : F := ⟨u, huF⟩
    have hpt : pick uF ∈ t := by
      exact (Set.finite_range pick).mem_toFinset.mpr ⟨uF, rfl⟩
    refine Set.mem_iUnion_of_mem (pick uF) (Set.mem_iUnion_of_mem hpt ?_)
    rw [hpick uF]
    exact hxu
  have hlimit : limit_point_compact X := by
    intro A hA
    obtain ⟨x, hxclosure, hxA⟩ := hright' A (Set.infinite_coe_iff.mp hA)
    exact ⟨x, hxA, mem_closure_iff_clusterPt.mp hxclosure⟩
  exact ⟨fun _ => hlimit, fun _ => hcount⟩
