import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X α : Type} [tα : Nonempty α] {f : α → Type} [Π a, TopologicalSpace (f a)] [∀ a, NormalSpace (f a)] (h : NormalSpace (∀ a, f a)): ∀ a, NormalSpace (f a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  -- not proved: the antecedent assumes `∀ a, NormalSpace (f a)`, which is the desired conclusion
  sorry
