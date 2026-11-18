import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_30_10_assumed
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {ι : Type*} [Fintype ι] {X : ι → Type*} [Nonempty ι] [∀ i, TopologicalSpace (X i)] (hX : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) : ∃ (s : Set (∀ i, X i)), Countable s ∧ Dense s := by
  letI : ∀ i, SeparableSpace (X i) := fun i => by
    let hprod := exercise_30_10_assumed (X := fun _ => X i) (fun _ => hX i)
    letI : SeparableSpace (∀ _ : ℕ, X i) := ⟨hprod⟩
    have heval : Function.Surjective (fun f : ℕ → X i => f 0) :=
      fun x => ⟨fun _ => x, rfl⟩
    exact heval.denseRange.separableSpace (continuous_apply 0)
  exact TopologicalSpace.exists_countable_dense _
