import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {M : Type*} [MetricSpace M] (A B : Set M) (hA : CompactSpace A) (hB : CompactSpace B) (hAB : A ∩ B = ∅) (hA0 : Nonempty A) (hB0 : Nonempty B) : ∃ (a0 : M), ∃ (b0 : M), ∀ (a : M) (b : M), a ∈ A → b ∈ B → dist a0 b0 ≤ dist a b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_46 {M : Type*} [MetricSpace M]
  {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
  (hAB : Disjoint A B) (hA₀ : A ≠ ∅) (hB₀ : B ≠ ∅) :
  ∃ a₀ b₀, a₀ ∈ A ∧ b₀ ∈ B ∧ ∀ (a : M) (b : M),
  a ∈ A → b ∈ B → dist a₀ b₀ ≤ dist a b := by
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA₀
  have hBne : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hB₀
  obtain ⟨p, hp, hmin⟩ := (hA.prod hB).exists_isMinOn
    ⟨(hAne.choose, hBne.choose), hAne.choose_spec, hBne.choose_spec⟩
    continuous_dist.continuousOn
  refine ⟨p.1, p.2, hp.1, hp.2, ?_⟩
  intro a b ha hb
  exact (isMinOn_iff.mp hmin) ⟨a, b⟩ ⟨ha, hb⟩
