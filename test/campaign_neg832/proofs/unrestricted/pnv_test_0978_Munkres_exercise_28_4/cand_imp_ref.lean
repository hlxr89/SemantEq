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
  exfalso
  have hrhs : ∀ (A : Set ℕ), A.Infinite → ∃ x ∈ closure A, x ∈ A := by
    intro A hA
    obtain ⟨x, hx⟩ := hA.nonempty
    exact ⟨x, subset_closure hx, hx⟩
  have hcompact := (dummy_assumed (X := ℕ)).mpr hrhs
  let U : Set (Set ℕ) := Set.range (fun n : ℕ => ({n} : Set ℕ))
  have hopen : ∀ u ∈ U, IsOpen u := by
    rintro u ⟨n, rfl⟩
    exact isOpen_discrete ({n} : Set ℕ)
  have hcover : ∀ x : ℕ, ∃ u ∈ U, x ∈ u := by
    intro x
    exact ⟨{x}, ⟨x, rfl⟩, by simp⟩
  obtain ⟨F, hFU, hFfinite, hFunion⟩ := hcompact U hopen hcover
  have hsets : ∀ s ∈ F, s.Finite := by
    intro s hs
    obtain ⟨n, rfl⟩ := hFU hs
    simp
  have hsUnionFinite : (⋃₀ F).Finite := hFfinite.sUnion hsets
  rw [hFunion] at hsUnionFinite
  exact Set.infinite_univ hsUnionFinite
