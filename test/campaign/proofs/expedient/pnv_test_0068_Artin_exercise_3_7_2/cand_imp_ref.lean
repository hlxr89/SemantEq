import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F V : Type*} [Field F] [Infinite F] [AddCommGroup V] [Module F V] : ¬ ∃ (s : Finset (Submodule F V)) (hs : ∀ (p : Submodule F V), p ∈ s → p ≠ ⊤), (⊤ : Submodule F V) = s.sup id := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_7_2 {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  classical
  intro hu
  apply dummy_assumed (F := K) (V := V)
  refine ⟨Finset.univ.image γ, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    exact h i
  · apply _root_.le_antisymm
    · intro x hx
      have hx' : x ∈ ⋃ i, (γ i : Set V) := by
        rw [hu]
        trivial
      simp only [Set.mem_iUnion] at hx'
      obtain ⟨i, hi⟩ := hx'
      have hle : γ i ≤ (Finset.univ.image γ).sup id :=
        Finset.le_sup (s := Finset.univ.image γ) (f := id)
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      exact hle hi
    · exact le_top
