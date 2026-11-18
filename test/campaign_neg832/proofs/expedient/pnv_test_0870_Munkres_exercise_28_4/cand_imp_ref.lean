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
  letI := hT1
  have hcover := (dummy_assumed (X := X)).2 (fun A _ => subset_closure)
  have hcc : countably_compact X := by
    intro U hU
    obtain ⟨F, hFrange, hFfinite, hFsUnion⟩ := hcover (Set.range U)
      (by rintro u ⟨n, rfl⟩; exact hU.1 n)
      (Set.countable_coe_iff.mpr (Set.countable_range U))
      (by rw [Set.sUnion_range]; exact Set.Subset.antisymm (fun _ _ => Set.mem_univ _) hU.2)
    classical
    letI : Finite F := hFfinite
    let hFset : F.Finite := Set.toFinite F
    let Ffin : Finset (Set X) := hFset.toFinset
    let g : Set X → ℕ := fun u => if hu : u ∈ F then Classical.choose (hFrange hu) else 0
    have hg (u : Set X) (hu : u ∈ F) : U (g u) = u := by
      simp only [g, dif_pos hu]
      exact Classical.choose_spec (hFrange hu)
    let t : Finset ℕ := Ffin.image g
    refine ⟨t, fun x _ => ?_⟩
    have hx : x ∈ ⋃₀ F := by simpa [hFsUnion]
    obtain ⟨u, huF, hxu⟩ := Set.mem_sUnion.mp hx
    have huFin : u ∈ Ffin := hFset.mem_toFinset.mpr huF
    have hgt : g u ∈ t := by
      apply Finset.mem_image.mpr
      exact ⟨u, huFin, rfl⟩
    exact Set.mem_iUnion.mpr ⟨g u, Set.mem_iUnion.mpr ⟨hgt, (hg u huF).symm ▸ hxu⟩⟩
  constructor
  · intro _ U hU
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨x, hx, clusterPt_principal.mpr (Or.inl hx)⟩
  · intro _
    exact hcc
