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
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [T1Space X] : (∀ (U : Set (Set X)), (∀ u ∈ U, IsOpen u) → (∀ x : X, ∃ u ∈ U, x ∈ u) → ∃ F ⊆ U, F.Finite ∧ (⋃₀ F) = univ) ↔ (∀ (A : Set X), A.Countable → A ≠ ∅ → ∃ x ∈ closure A, x ∈ A) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_4 {X : Type*}
  [TopologicalSpace X] (hT1 : T1Space X) :
  countably_compact X ↔ limit_point_compact X := by
  letI : T1Space X := hT1
  have hcand := dummy_assumed (X := X)
  have hright : ∀ (A : Set X), A.Countable → A ≠ ∅ → ∃ x ∈ closure A, x ∈ A := by
    intro A _ hA
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hA
    exact ⟨x, subset_closure hx, hx⟩
  have hcover := hcand.mpr hright
  have hcount : countably_compact X := by
    classical
    intro U hU
    let C : Set (Set X) := Set.range U
    obtain ⟨F, hFC, hFfin, hFuniv⟩ := hcover C
      (by rintro u ⟨i, rfl⟩; exact hU.1 i)
      (by
        intro x
        obtain ⟨i, hxi⟩ := mem_iUnion.mp (hU.2 (mem_univ x))
        exact ⟨U i, ⟨i, rfl⟩, hxi⟩)
    let f : Set X → ℕ := fun u ↦ if hu : u ∈ F then Classical.choose (hFC hu) else 0
    have hf (u : Set X) (hu : u ∈ F) : U (f u) = u := by
      simp only [f, dif_pos hu]
      exact Classical.choose_spec (hFC hu)
    let t : Finset ℕ := hFfin.toFinset.image f
    refine ⟨t, ?_⟩
    intro x _
    have hx : x ∈ ⋃₀ F := hFuniv.symm ▸ mem_univ x
    obtain ⟨u, huF, hxu⟩ := mem_sUnion.mp hx
    exact mem_iUnion₂.mpr ⟨f u,
      Finset.mem_image.mpr ⟨u, hFfin.mem_toFinset.mpr huF, rfl⟩,
      by simpa [hf u huF] using hxu⟩
  have hlimit : limit_point_compact X := by
    intro U hU
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨x, hx, mem_closure_iff_clusterPt.mp (subset_closure hx)⟩
  exact ⟨fun _ ↦ hlimit, fun _ ↦ hcount⟩
