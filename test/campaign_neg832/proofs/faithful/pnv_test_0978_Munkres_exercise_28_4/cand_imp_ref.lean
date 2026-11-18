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
  have hcover : ∀ (U : Set (Set X)), (∀ u ∈ U, IsOpen u) →
      (∀ x : X, ∃ u ∈ U, x ∈ u) → ∃ F ⊆ U, F.Finite ∧ (⋃₀ F) = univ :=
    (dummy_assumed (X := X)).2 (by
      intro A hA
      obtain ⟨x, hx⟩ := hA.nonempty
      exact ⟨x, subset_closure hx, hx⟩)
  have hcount : countably_compact X := by
    intro U hU
    obtain ⟨F, hFrange, hFfinite, hFunion⟩ := hcover (range U)
      (by rintro V ⟨i, rfl⟩; exact hU.1 i)
      (by
        intro x
        rcases mem_iUnion.mp (hU.2 (mem_univ x)) with ⟨i, hxi⟩
        exact ⟨U i, mem_range_self i, hxi⟩)
    classical
    choose index hindex using fun V : F ↦ hFrange V.property
    letI : Fintype F := hFfinite.fintype
    let t : Finset ℕ := Finset.univ.image index
    refine ⟨t, ?_⟩
    intro x hx
    have hx' : x ∈ ⋃₀ F := by simpa [hFunion]
    rcases mem_sUnion.mp hx' with ⟨V, hVF, hxV⟩
    let v : F := ⟨V, hVF⟩
    have hiv : U (index v) = V := hindex v
    refine mem_iUnion.2 ⟨index v, mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.2 ⟨v, Finset.mem_univ v, rfl⟩
    · simpa [hiv] using hxV
  have hclosure : ∀ (A : Set X), A.Infinite → ∃ x ∈ closure A, x ∈ A :=
    (dummy_assumed (X := X)).1 hcover
  constructor
  · intro _
    intro U hU
    obtain ⟨x, hxclosure, hx⟩ := hclosure U (Set.infinite_coe_iff.1 hU)
    exact ⟨x, hx, mem_closure_iff_clusterPt.1 hxclosure⟩
  · intro _
    exact hcount
