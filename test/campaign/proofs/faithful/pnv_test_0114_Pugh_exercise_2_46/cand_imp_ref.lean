import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {M : Type*} [PseudoMetricSpace M] {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hA0 : A.Nonempty) (hB0 : B.Nonempty) : ∃ a ∈ A, ∃ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, dist a b ≤ dist a' b' := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_46 {M : Type*} [MetricSpace M]
  {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
  (hAB : Disjoint A B) (hA₀ : A ≠ ∅) (hB₀ : B ≠ ∅) :
  ∃ a₀ b₀, a₀ ∈ A ∧ b₀ ∈ B ∧ ∀ (a : M) (b : M),
  a ∈ A → b ∈ B → dist a₀ b₀ ≤ dist a b := by
  have hA0 : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA₀
  have hB0 : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hB₀
  obtain ⟨a₀, ha₀, b₀, hb₀, hmin⟩ :=
    dummy_assumed hA hB hAB hA0 hB0
  exact ⟨a₀, b₀, ha₀, hb₀, fun a b ha hb => hmin a ha b hb⟩
