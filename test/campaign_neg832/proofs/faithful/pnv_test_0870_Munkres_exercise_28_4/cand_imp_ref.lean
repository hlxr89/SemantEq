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
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [T1Space X] : (∀ (U : Set (Set X)), (∀ u ∈ U, IsOpen u) → (Countable U) → (⋃₀ U = univ) → ∃ F ⊆ U, (Finite F) ∧ (⋃₀ F = univ)) ↔ (∀ (A : Set X), (Countable A) → (A ⊆ closure A)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_4 {X : Type*}
  [TopologicalSpace X] (hT1 : T1Space X) :
  countably_compact X ↔ limit_point_compact X := by
  classical
  letI : T1Space X := hT1
  have hcover := (dummy_assumed (X := X)).mpr (by
    intro A _
    exact subset_closure)
  have hcompact : countably_compact X := by
    intro U hU
    obtain ⟨F, hFU, hF, hFcover⟩ := hcover (Set.range U)
      (by rintro u ⟨n, rfl⟩; exact hU.1 n)
      (Set.countable_range U)
      (by
        apply Set.Subset.antisymm
        · intro x _
          exact Set.mem_univ x
        · intro x hx
          obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp (hU.2 hx)
          exact Set.mem_sUnion.mpr ⟨U n, ⟨n, rfl⟩, hxn⟩)
    letI : Finite F := hF
    have hFset : F.Finite := Set.toFinite F
    let chooseIndex : Set X → ℕ := fun u =>
      if hu : u ∈ F then Classical.choose (hFU hu) else 0
    let t : Finset ℕ := hFset.toFinset.image chooseIndex
    refine ⟨t, ?_⟩
    intro x hx
    have hx' : x ∈ ⋃₀ F := by simpa [hFcover]
    obtain ⟨u, huF, hxu⟩ := Set.mem_sUnion.mp hx'
    have huEq : U (chooseIndex u) = u := by
      simpa [chooseIndex, huF] using Classical.choose_spec (hFU huF)
    apply Set.mem_iUnion.mpr
    refine ⟨chooseIndex u, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨u, by simpa using huF, rfl⟩
    · rw [huEq]
      exact hxu
  constructor
  · intro _
    intro U hU
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨x, hx, mem_closure_iff_clusterPt.mp (subset_closure hx)⟩
  · intro _
    exact hcompact
