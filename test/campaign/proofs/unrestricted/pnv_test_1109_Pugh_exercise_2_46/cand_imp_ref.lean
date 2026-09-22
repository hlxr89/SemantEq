import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {M : Type*} [MetricSpace M] {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty) (h_disjoint : Disjoint A B) : ∃ a₀ ∈ A, ∃ b₀ ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a₀ b₀ ≤ dist a b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_46 {M : Type*} [MetricSpace M]
  {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
  (hAB : Disjoint A B) (hA₀ : A ≠ ∅) (hB₀ : B ≠ ∅) :
  ∃ a₀ b₀, a₀ ∈ A ∧ b₀ ∈ B ∧ ∀ (a : M) (b : M),
  a ∈ A → b ∈ B → dist a₀ b₀ ≤ dist a b := by
  rcases dummy_assumed hA hB (Set.nonempty_iff_ne_empty.mpr hA₀)
      (Set.nonempty_iff_ne_empty.mpr hB₀) hAB with ⟨a₀, ha₀, b₀, hb₀, hmin⟩
  exact ⟨a₀, b₀, ha₀, hb₀, fun a b ha hb => hmin a ha b hb⟩
