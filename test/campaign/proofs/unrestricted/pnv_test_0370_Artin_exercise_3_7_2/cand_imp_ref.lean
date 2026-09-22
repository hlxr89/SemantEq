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
    rcases Finset.mem_image.mp hW with ⟨i, -, rfl⟩
    exact h i
  have hfin := dummy_assumed (S := S) hS
  simpa [S] using hfin
