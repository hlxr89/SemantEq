import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_21a_assumed {X : Type*} [MetricSpace X]
  (K F : Set X) (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (p q : X), p ∈ K → q ∈ F → dist p q > δ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy [PseudoMetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (hd : Disjoint K F) : ∃ (δ : ℝ) (H : δ > 0), ∀ {x y : X}, x ∈ K → y ∈ F → dist x y > δ := by
  have hK' : IsCompact (SeparationQuotient.mk '' K) :=
    hK.image SeparationQuotient.continuous_mk
  have hF' : IsClosed (SeparationQuotient.mk '' F) :=
    SeparationQuotient.isClosedMap_mk F hF
  have hd' : Disjoint (SeparationQuotient.mk '' K) (SeparationQuotient.mk '' F) := by
    rw [Set.disjoint_left]
    intro z hzK hzF
    rcases hzK with ⟨x, hx, rfl⟩
    rcases hzF with ⟨y, hy, hxy⟩
    have hxinF : x ∈ F := by
      rw [← SeparationQuotient.preimage_image_mk_closed hF]
      exact ⟨y, hy, hxy⟩
    exact Set.disjoint_left.mp hd hx hxinF
  obtain ⟨δ, hδ, hbound⟩ := exercise_4_21a_assumed
    (SeparationQuotient.mk '' K) (SeparationQuotient.mk '' F) hK' hF' hd'
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy
  have hxy := hbound (SeparationQuotient.mk x) (SeparationQuotient.mk y)
    ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  rw [SeparationQuotient.dist_mk] at hxy
  exact hxy
