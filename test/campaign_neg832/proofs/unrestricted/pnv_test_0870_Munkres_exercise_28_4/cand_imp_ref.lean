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
  classical
  letI : T1Space X := hT1
  have hcover : ∀ (U : Set (Set X)), (∀ u ∈ U, IsOpen u) → (Countable U) → (⋃₀ U = univ) → ∃ F ⊆ U, (Finite F) ∧ (⋃₀ F = univ) :=
    (dummy_assumed (X := X)).mpr (fun A hA ↦ subset_closure)
  constructor
  · intro hcc U hU
    obtain ⟨x, hx⟩ := (Set.infinite_coe_iff.mp hU).nonempty
    exact ⟨x, hx, mem_closure_iff_clusterPt.mp (subset_closure hx)⟩
  · intro hlpc U hU
    let C : Set (Set X) := Set.range U
    have hCopen : ∀ u ∈ C, IsOpen u := by
      rintro u ⟨n, rfl⟩
      exact hU.1 n
    have hCcount : Countable C := Set.countable_range U
    have hCunion : ⋃₀ C = (univ : Set X) := by
      apply Set.Subset.antisymm (Set.subset_univ _)
      intro x hx
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp (hU.2 hx)
      exact Set.mem_sUnion.mpr ⟨U n, ⟨n, rfl⟩, hxn⟩
    obtain ⟨F, hFC, hFfinite, hFunion⟩ := hcover C hCopen hCcount hCunion
    letI : Finite F := hFfinite
    have hFset : F.Finite := Set.toFinite F
    let t : Finset ℕ := hFset.toFinset.image (Function.invFun U)
    refine ⟨t, ?_⟩
    intro x hx
    have hxs : x ∈ ⋃₀ F := by simpa [hFunion]
    obtain ⟨u, huF, hxu⟩ := Set.mem_sUnion.mp hxs
    have huRange : u ∈ Set.range U := hFC huF
    have huEq : U (Function.invFun U u) = u := Function.invFun_eq (Set.mem_range.mp huRange)
    apply Set.mem_iUnion₂.mpr
    refine ⟨Function.invFun U u, ?_, ?_⟩
    · rw [show t = hFset.toFinset.image (Function.invFun U) by rfl,
          Finset.mem_image]
      exact ⟨u, hFset.mem_toFinset.mpr huF, rfl⟩
    · simpa [huEq] using hxu
