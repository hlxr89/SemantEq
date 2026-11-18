import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_32_2a_assumed
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : T2Space (Π i, X i)) :
  ∀ i, T2Space (X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] (h : T2Space (∀ i, X i)) (i : ι) : T2Space (X i) := by
  classical
  by_cases hi : Nonempty (X i)
  · letI : Nonempty (X i) := hi
    have hfactor := exercise_32_2a_assumed
      (ι := Unit) (X := fun _ => X i) (fun _ => hi) (by infer_instance)
    exact hfactor ()
  · have hempty : IsEmpty (X i) := not_nonempty_iff.mp hi
    letI : IsEmpty (X i) := hempty
    exact inferInstance
