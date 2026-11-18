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
  exfalso
  obtain ⟨a, ha, b, hb, hab⟩ := dummy_assumed
    (M := ℝ) (A := {0, 100}) (B := {40, 60}) (by simp)
    (by simp) (by simp [Set.disjoint_left]) (by simp) (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl)
  · have := hab 100 (by simp) 40 (by simp)
    norm_num [Real.dist_eq] at this
  · have := hab 0 (by simp) 40 (by simp)
    norm_num [Real.dist_eq] at this
  · have := hab 100 (by simp) 60 (by simp)
    norm_num [Real.dist_eq] at this
  · have := hab 0 (by simp) 60 (by simp)
    norm_num [Real.dist_eq] at this
