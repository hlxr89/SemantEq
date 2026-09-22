import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_7_2_assumed {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {F : Type*} [Field F] [Infinite F] {V : Type*} [AddCommGroup V] [Module F V] (s : Finset (Submodule F V)) (hs : ∀ W ∈ s, W ≠ ⊤) : (⋃ W ∈ s, (W : Set V)) ≠ (⊤ : Submodule F V) := by
  simpa only [Set.iUnion_subtype] using
    (exercise_3_7_2_assumed (γ := fun W : {W // W ∈ s} => W.1)
      (fun W => hs W.1 W.2))
