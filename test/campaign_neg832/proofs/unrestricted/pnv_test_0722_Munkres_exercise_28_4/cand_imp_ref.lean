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
  have hrhs : ∀ (A : Set X), A.Countable → A ≠ ∅ → ∃ x ∈ closure A, x ∈ A := by
    intro A _ hA
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hA
    exact ⟨x, subset_closure hx, hx⟩
  have hcompact := dummy_assumed.mpr hrhs
  have hcount : countably_compact X := by
    intro U hU
    obtain ⟨F, hFrange, hFfinite, hFunion⟩ :=
      hcompact (Set.range U) (by
        intro u hu
        obtain ⟨i, rfl⟩ := hu
        exact hU.1 i) (by
        intro x
        have hx : x ∈ ⋃ i, U i := hU.2 (Set.mem_univ x)
        simp only [Set.mem_iUnion] at hx
        obtain ⟨i, hi⟩ := hx
        exact ⟨U i, ⟨i, rfl⟩, hi⟩)
    classical
    letI : Fintype F := hFfinite.fintype
    let n : F → ℕ := fun u => Classical.choose (hFrange u.property)
    let t : Finset ℕ := Finset.univ.image n
    refine ⟨t, ?_⟩
    intro x _
    have hxunion : x ∈ ⋃₀ F := by simpa [hFunion]
    obtain ⟨u, huF, hxu⟩ := Set.mem_sUnion.mp hxunion
    let usub : F := ⟨u, huF⟩
    have hUn : U (n usub) = u := Classical.choose_spec (hFrange huF)
    have hnt : n usub ∈ t := by
      exact Finset.mem_image.mpr ⟨usub, Finset.mem_univ usub, rfl⟩
    simp only [Set.mem_iUnion]
    exact ⟨n usub, ⟨hnt, hUn ▸ hxu⟩⟩
  have hlimit : limit_point_compact X := by
    intro U hU
    obtain ⟨x, hx⟩ := hU.nonempty
    refine ⟨x, hx, ?_⟩
    exact mem_closure_iff_clusterPt.mp (subset_closure hx)
  exact ⟨fun _ => hlimit, fun _ => hcount⟩
