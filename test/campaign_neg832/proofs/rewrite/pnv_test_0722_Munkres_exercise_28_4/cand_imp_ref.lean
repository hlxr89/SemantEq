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
  have hright : ∀ (A : Set X), A.Countable → A ≠ ∅ → ∃ x ∈ closure A, x ∈ A := by
    intro A _ hA
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hA
    exact ⟨x, subset_closure hx, hx⟩
  have hopen := dummy_assumed (X := X) |>.mpr hright
  have hcount : countably_compact X := by
    intro U hU
    obtain ⟨F, hFrange, hFfinite, hFuniv⟩ := hopen (range U) (by
      intro V hV
      obtain ⟨i, rfl⟩ := hV
      exact hU.1 i) (by
      intro x
      obtain ⟨i, hxi⟩ := mem_iUnion.mp (hU.2 (mem_univ x))
      exact ⟨U i, mem_range_self i, hxi⟩)
    classical
    let f : Set X → ℕ := fun V => if hV : V ∈ F then Classical.choose (hFrange hV) else 0
    have hf (V : Set X) (hV : V ∈ F) : U (f V) = V := by
      simp only [f, dif_pos hV]
      exact Classical.choose_spec (hFrange hV)
    let t : Finset ℕ := hFfinite.toFinset.image f
    refine ⟨t, ?_⟩
    intro x _
    have hx : x ∈ ⋃₀ F := by rw [hFuniv]; exact mem_univ x
    obtain ⟨V, hVF, hxV⟩ := mem_sUnion.mp hx
    have hft : f V ∈ t := by
      exact Finset.mem_image.mpr ⟨V, (Set.Finite.mem_toFinset hFfinite).mpr hVF, rfl⟩
    exact mem_iUnion₂.mpr ⟨f V, hft, (hf V hVF).symm ▸ hxV⟩
  have hlimit_of_countably : countably_compact X → limit_point_compact X := by
    intro _ U hU
    letI : Infinite U := hU
    obtain ⟨x⟩ := Infinite.nonempty U
    exact ⟨x, x.2, mem_closure_iff_clusterPt.mp (subset_closure x.2)⟩
  exact ⟨fun _ => hlimit_of_countably hcount, fun _ => hcount⟩
