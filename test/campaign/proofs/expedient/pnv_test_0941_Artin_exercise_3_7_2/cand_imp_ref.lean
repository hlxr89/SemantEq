import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] [Infinite F] {V : Type*} [AddCommGroup V] [Module F V] (s : Finset (Submodule F V)) (hs : ∀ W ∈ s, W ≠ ⊤) : (⋃ W ∈ s, (W : Set V)) ≠ (⊤ : Submodule F V) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_7_2 {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  classical
  simpa using
    (dummy_assumed (Finset.univ.image γ) (by
      intro W hW
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hW
      exact h i))
