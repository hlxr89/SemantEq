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
  letI : T1Space X := hT1
  have hright : ∀ (A : Set X), (Countable A) → (A ⊆ closure A) := by
    intro A hA
    exact subset_closure
  have hcover := (dummy_assumed (X := X)).mpr hright
  have hcc : countably_compact X := by
    intro U hU
    have hopen : ∀ u ∈ Set.range U, IsOpen u := by
      intro u hu
      obtain ⟨n, rfl⟩ := hu
      exact hU.1 n
    have hcount : Countable (Set.range U) := Set.countable_range U
    have hcoverU : ⋃₀ Set.range U = (univ : Set X) := by
      rw [Set.sUnion_range]
      exact Set.eq_univ_of_univ_subset hU.2
    obtain ⟨F, hFsub, hFfinite, hFunion⟩ := hcover (Set.range U) hopen hcount hcoverU
    classical
    letI : Finite F := hFfinite
    have hFinRange : ↑F.toFinset ⊆ U '' (univ : Set ℕ) := by
      simpa only [Set.coe_toFinset, Set.image_univ] using hFsub
    obtain ⟨t, htuniv, ht⟩ := Finset.subset_set_image_iff.mp hFinRange
    refine ⟨t, ?_⟩
    intro x hx
    have hxF : x ∈ ⋃₀ F := by rw [hFunion]; exact hx
    obtain ⟨u, huF, hxu⟩ := Set.mem_sUnion.mp hxF
    have huFin : u ∈ F.toFinset := by simpa using huF
    rw [← ht] at huFin
    obtain ⟨n, hnt, hnU⟩ := Finset.mem_image.mp huFin
    simp only [Set.mem_iUnion]
    exact ⟨n, hnt, hnU ▸ hxu⟩
  have hlpc : limit_point_compact X := by
    intro U hU
    obtain ⟨x, hx⟩ := Set.Infinite.nonempty (Set.infinite_coe_iff.mp hU)
    exact ⟨x, hx, mem_closure_iff_clusterPt.mp (subset_closure hx)⟩
  exact ⟨fun _ ↦ hlpc, fun _ ↦ hcc⟩
