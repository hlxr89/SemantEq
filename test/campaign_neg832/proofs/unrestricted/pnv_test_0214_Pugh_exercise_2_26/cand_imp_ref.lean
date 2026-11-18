import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type u} [TopologicalSpace α] {s : Set α} : IsOpen s ↔ ∀ x, x ∉ closure (sᶜ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hM =>
      letI := hM
      have hU : U = ∅ := by
        ext x
        exact isEmptyElim x
      subst U
      simp
  | inr hM =>
      letI := hM
      exfalso
      have h := (dummy_assumed (α := M) (s := (∅ : Set M))).mp isOpen_empty
      have hx := h (Classical.choice hM)
      simpa using hx
