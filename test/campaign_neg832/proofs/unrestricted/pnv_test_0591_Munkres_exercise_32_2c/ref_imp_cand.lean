import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_32_2c_assumed
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X α : Type} [tα : Nonempty α] {f : α → Type} [Π a, TopologicalSpace (f a)] [∀ a, NormalSpace (f a)] (h : NormalSpace (∀ a, f a)): ∀ a, NormalSpace (f a) := by
  intro a
  infer_instance
