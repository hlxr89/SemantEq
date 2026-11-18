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
  classical
  have hlpc : limit_point_compact X := by
    intro U hU
    obtain ⟨x, hx⟩ := (Set.infinite_coe_iff.mp hU).nonempty
    exact ⟨x, hx, mem_closure_iff_clusterPt.mp (subset_closure hx)⟩
  have hcc : countably_compact X :=
    (exercise_28_4_assumed (X := X) (inferInstance : T1Space X)).mpr hlpc
  constructor
  · intro hcover A hA
    exact subset_closure
  · intro hclosure U hopen hcount hUnion
    by_cases hUne : U.Nonempty
    · letI : Countable U := hcount
      letI : Nonempty U := hUne.to_subtype
      obtain ⟨f, hf⟩ := exists_surjective_nat U
      let g : ℕ → Set X := fun n ↦ (f n : Set X)
      obtain ⟨t, ht⟩ := hcc g ⟨
        fun n ↦ hopen (g n) (f n).property,
        by
          intro x hx
          have hxs : x ∈ ⋃₀ U := by simpa [hUnion]
          obtain ⟨u, huU, hxu⟩ := Set.mem_sUnion.mp hxs
          obtain ⟨n, hn⟩ := hf ⟨u, huU⟩
          have hgnu : g n = u := congrArg Subtype.val hn
          exact Set.mem_iUnion.mpr ⟨n, hgnu.symm ▸ hxu⟩
        ⟩
      let F : Set (Set X) := g '' (t : Set ℕ)
      refine ⟨F, ?_, Set.Finite.image g t.finite_toSet, ?_⟩
      · rintro v ⟨n, hn, rfl⟩
        exact (f n).property
      · apply Set.Subset.antisymm (Set.subset_univ _)
        intro x hx
        obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp (ht hx)
        apply Set.mem_sUnion.mpr
        exact ⟨g n, ⟨n, hn, rfl⟩, hxn⟩
    · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hUne
      subst U
      exact ⟨∅, Set.empty_subset _, Set.finite_empty, hUnion⟩
