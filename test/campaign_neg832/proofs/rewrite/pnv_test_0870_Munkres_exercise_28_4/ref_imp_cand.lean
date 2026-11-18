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
theorem exercise_28_4_assumed {X : Type*}
  [TopologicalSpace X] (hT1 : T1Space X) :
  countably_compact X ↔ limit_point_compact X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X : Type*} [TopologicalSpace X] [T1Space X] : (∀ (U : Set (Set X)), (∀ u ∈ U, IsOpen u) → (Countable U) → (⋃₀ U = univ) → ∃ F ⊆ U, (Finite F) ∧ (⋃₀ F = univ)) ↔ (∀ (A : Set X), (Countable A) → (A ⊆ closure A)) := by
  have hlpc : limit_point_compact X := by
    intro U hU
    obtain ⟨x, hx⟩ := Set.Infinite.nonempty (Set.infinite_coe_iff.mp hU)
    exact ⟨x, hx, mem_closure_iff_clusterPt.mp (subset_closure hx)⟩
  have hcc : countably_compact X :=
    (exercise_28_4_assumed (X := X) (inferInstance : T1Space X)).mpr hlpc
  constructor
  · intro hleft A hcount
    exact subset_closure
  · intro hright U hopen hcount hcover
    classical
    by_cases hU : U.Nonempty
    · obtain ⟨f, hf⟩ :=
        Set.Countable.exists_surjective hU (Set.countable_coe_iff.mp hcount)
      let V : ℕ → Set X := fun n ↦ (f n : Set X)
      have hopenV : ∀ n, IsOpen (V n) := by
        intro n
        exact hopen (f n) (f n).property
      have hcoverV : (univ : Set X) ⊆ ⋃ n, V n := by
        intro x hx
        have hxU : x ∈ ⋃₀ U := by rw [hcover]; exact hx
        obtain ⟨u, huU, hxu⟩ := Set.mem_sUnion.mp hxU
        obtain ⟨n, hn⟩ := hf ⟨u, huU⟩
        apply Set.mem_iUnion.mpr
        refine ⟨n, ?_⟩
        change x ∈ (f n : Set X)
        rw [hn]
        exact hxu
      obtain ⟨t, ht⟩ := hcc V ⟨hopenV, hcoverV⟩
      let F : Set (Set X) := V '' (t : Set ℕ)
      refine ⟨F, ?_, (Set.toFinite F), ?_⟩
      · intro u hu
        obtain ⟨n, hn, rfl⟩ := hu
        exact (f n).property
      · apply Set.eq_univ_of_univ_subset
        intro x hx
        have hxV : x ∈ ⋃ n ∈ t, V n := ht hx
        simp only [Set.mem_iUnion] at hxV
        obtain ⟨n, hn, hxn⟩ := hxV
        exact Set.mem_sUnion.mpr ⟨V n, ⟨n, hn, rfl⟩, hxn⟩
    · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
      refine ⟨∅, Set.empty_subset U, Set.finite_empty, ?_⟩
      simpa only [hUempty, Set.sUnion_empty] using hcover
