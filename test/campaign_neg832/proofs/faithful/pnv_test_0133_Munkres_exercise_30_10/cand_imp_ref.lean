import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {ι : Type*} [Fintype ι] {X : ι → Type*} [Nonempty ι] [∀ i, TopologicalSpace (X i)] (hX : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) : ∃ (s : Set (∀ i, X i)), Countable s ∧ Dense s := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_30_10
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  letI : ∀ i, SeparableSpace (X i) := fun i => by
    let hprod := dummy_assumed (ι := Fin 1) (X := fun _ => X i) (fun _ => h i)
    letI : SeparableSpace (Fin 1 → X i) := ⟨hprod⟩
    have heval : Function.Surjective (fun f : Fin 1 → X i => f 0) :=
      fun x => ⟨fun _ => x, rfl⟩
    exact heval.denseRange.separableSpace (continuous_apply 0)
  exact TopologicalSpace.exists_countable_dense _
