import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {M : Type*} [PseudoMetricSpace M] {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hA0 : A.Nonempty) (hB0 : B.Nonempty) : ∃ a ∈ A, ∃ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, dist a' b ≤ dist a b' := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_46 {M : Type*} [MetricSpace M]
  {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
  (hAB : Disjoint A B) (hA₀ : A ≠ ∅) (hB₀ : B ≠ ∅) :
  ∃ a₀ b₀, a₀ ∈ A ∧ b₀ ∈ B ∧ ∀ (a : M) (b : M),
  a ∈ A → b ∈ B → dist a₀ b₀ ≤ dist a b := by
  have hAc : IsCompact ({0, 10} : Set ℝ) :=
    isCompact_singleton.union isCompact_singleton
  have hBc : IsCompact ({4, 6} : Set ℝ) :=
    isCompact_singleton.union isCompact_singleton
  have hdis : Disjoint ({0, 10} : Set ℝ) ({4, 6} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with (rfl | rfl) <;> rcases hy with (h | h) <;> norm_num at h
  have hAne : ({0, 10} : Set ℝ).Nonempty := ⟨0, by simp⟩
  have hBne : ({4, 6} : Set ℝ).Nonempty := ⟨4, by simp⟩
  obtain ⟨a, ha, b, hb, hab⟩ := dummy_assumed hAc hBc hdis hAne hBne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with (rfl | rfl)
  · rcases hb with (rfl | rfl)
    · have := hab 10 (by simp) 4 (by simp)
      norm_num [Real.dist_eq] at this
    · have := hab 0 (by simp) 4 (by simp)
      norm_num [Real.dist_eq] at this
  · rcases hb with (rfl | rfl)
    · have := hab 10 (by simp) 6 (by simp)
      norm_num [Real.dist_eq] at this
    · have := hab 0 (by simp) 6 (by simp)
      norm_num [Real.dist_eq] at this
