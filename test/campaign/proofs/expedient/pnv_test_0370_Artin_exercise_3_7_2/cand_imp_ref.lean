import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] [Infinite F] {V : Type*} [AddCommGroup V] [Module F V] {S : Finset (Submodule F V)} (hS : ∀ W ∈ S, W ≠ ⊤) : (⋃ W ∈ S, (W : Set V)) ≠ (⊤ : Submodule F V) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_7_2 {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  classical
  let S : Finset (Submodule K V) := Finset.univ.image γ
  have hS : ∀ W ∈ S, W ≠ ⊤ := by
    intro W hW
    simp only [S, Finset.mem_image] at hW
    obtain ⟨i, _, rfl⟩ := hW
    exact h i
  simpa [S] using dummy_assumed hS
