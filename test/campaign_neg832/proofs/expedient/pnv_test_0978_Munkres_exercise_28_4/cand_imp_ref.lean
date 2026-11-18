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
  have hr : ∀ (A : Set ℕ), A.Infinite → ∃ x ∈ closure A, x ∈ A := by
    intro A hA
    obtain ⟨x, hx⟩ := hA.nonempty
    exact ⟨x, subset_closure hx, hx⟩
  have hc := (dummy_assumed (X := ℕ)).2 hr
  let U : Set (Set ℕ) := Set.range (fun n => ({n} : Set ℕ))
  obtain ⟨F, hFU, hF, hcover⟩ := hc U
    (by rintro u ⟨n, rfl⟩; exact isOpen_discrete _)
    (by intro x; exact ⟨{x}, ⟨x, rfl⟩, by simp⟩)
  have hsfin : (⋃₀ F).Finite := hF.sUnion (by
    intro u hu
    obtain ⟨n, rfl⟩ := hFU hu
    exact Set.finite_singleton n)
  rw [hcover] at hsfin
  exact Set.infinite_univ hsfin
