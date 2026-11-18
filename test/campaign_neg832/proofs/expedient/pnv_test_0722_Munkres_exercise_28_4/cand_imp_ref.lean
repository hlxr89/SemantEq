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
  letI := hT1
  have hr : ∀ (A : Set X), A.Countable → A ≠ ∅ → ∃ x ∈ closure A, x ∈ A := by
    intro A _ hA
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hA
    exact ⟨x, subset_closure hx, hx⟩
  have hc := dummy_assumed.mpr hr
  have hcount : countably_compact X := by
    intro U hU
    classical
    obtain ⟨F, hFrange, hFfin, hFunion⟩ := hc (range U)
      (by rintro V ⟨i, rfl⟩; exact hU.1 i)
      (by intro x; rcases mem_iUnion.mp (hU.2 (mem_univ x)) with ⟨i, hxi⟩
          exact ⟨U i, ⟨i, rfl⟩, hxi⟩)
    let f : F → ℕ := fun V => Classical.choose (hFrange V.2)
    have hf (V : F) : U (f V) = V.1 := Classical.choose_spec (hFrange V.2)
    letI : Fintype F := hFfin.fintype
    refine ⟨Finset.univ.image f, ?_⟩
    intro x _
    have hxF : x ∈ ⋃₀ F := by rw [hFunion]; exact mem_univ x
    obtain ⟨V, hVF, hV⟩ := mem_sUnion.mp hxF
    have ht : f ⟨V, hVF⟩ ∈ Finset.univ.image f := by
      apply Finset.mem_image.mpr
      exact ⟨⟨V, hVF⟩, Finset.mem_univ _, rfl⟩
    apply mem_iUnion₂.mpr
    exact ⟨f ⟨V, hVF⟩, ht, by simpa [hf ⟨V, hVF⟩] using hV⟩
  constructor
  · intro _ U hU
    letI : Infinite U := hU
    obtain ⟨⟨x, hx⟩⟩ := Infinite.nonempty U
    exact ⟨x, hx, (mem_closure_iff_clusterPt.1 (subset_closure hx))⟩
  · intro _
    exact hcount
