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
  have hd' : Disjoint (SeparationQuotient.mk '' K) (SeparationQuotient.mk '' F) := by
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    have hxF : x ∈ F := by
      rw [← SeparationQuotient.preimage_image_mk_closed hF]
      exact ⟨y, hy, hyz.trans hxz.symm⟩
    exact Set.disjoint_left.1 hd hx hxF
  obtain ⟨δ, hδ, hdist⟩ := exercise_4_21a_assumed
    (SeparationQuotient.mk '' K) (SeparationQuotient.mk '' F)
    (hK.image SeparationQuotient.continuous_mk)
    (SeparationQuotient.isClosedMap_mk F hF) hd'
  refine ⟨δ, hδ, fun {x y} hx hy => ?_⟩
  simpa only [SeparationQuotient.dist_mk] using
    hdist (SeparationQuotient.mk x) (SeparationQuotient.mk y) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
