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
theorem dummy {ι : Type*} {X : ι → Type*} [∀ α, TopologicalSpace (X α)] [∀ α, Nonempty (X α)] (h : NormalSpace (Π α, X α)) (α : ι) : NormalSpace (X α) := by
  exact exercise_32_2c_assumed (fun i => inferInstance) h α
