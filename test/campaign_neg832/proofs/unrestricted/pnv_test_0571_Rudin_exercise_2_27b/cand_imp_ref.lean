import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (E : Set ℝ) [hs : Uncountable E] : Set.Countable (frontier E \ E) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_27b (k : ℕ) (E P : Set (EuclideanSpace ℝ (Fin k)))
  (hE : ¬ Set.Countable E)
  (hP : P = {x | ∀ U ∈ 𝓝 x, ¬ Set.Countable (U ∩ E)}) :
  Set.Countable (E \ P) := by
  let D : Set ℝ := Set.Iio 0 ∪ Set.range ((↑) : ℚ → ℝ)
  let f : ℝ → D := fun x => ⟨-Real.exp x, Or.inl (neg_neg_of_pos (Real.exp_pos x))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Real.exp_injective
    exact neg_injective (Subtype.mk.inj hxy)
  letI : Uncountable D := hf.uncountable
  have hD := dummy_assumed D
  have hdense : Dense D := by
    apply Rat.denseRange_cast.mono
    intro x hx
    exact Or.inr hx
  have hsubset : Set.Ioi (0 : ℝ) ⊆ (frontier D \ D) ∪ Set.range ((↑) : ℚ → ℝ) := by
    intro x hx
    by_cases hrat : x ∈ Set.range ((↑) : ℚ → ℝ)
    · exact Or.inr hrat
    · apply Or.inl
      constructor
      · rw [frontier_eq_closure_inter_closure]
        constructor
        · rw [hdense.closure_eq]
          exact Set.mem_univ x
        · rw [mem_closure_iff_frequently]
          have hirr_cl : x ∈ closure {y : ℝ | Irrational y} := by
            rw [dense_irrational.closure_eq]
            exact Set.mem_univ x
          have hirr : ∃ᶠ y in 𝓝 x, Irrational y :=
            mem_closure_iff_frequently.mp hirr_cl
          refine (hirr.and_eventually (Ioi_mem_nhds hx)).mono ?_
          rintro y ⟨hyirr, hypos⟩
          simp only [Set.mem_compl_iff, D, Set.mem_union, Set.mem_Iio,
            Set.mem_range, not_or]
          constructor
          · exact not_lt_of_ge (le_of_lt hypos)
          · intro hyq
            obtain ⟨q, rfl⟩ := hyq
            exact Rat.not_irrational q hyirr
      · simp only [D, Set.mem_union, Set.mem_Iio, Set.mem_range, not_or]
        exact ⟨not_lt_of_ge (le_of_lt hx), hrat⟩
  have hIoi : (Set.Ioi (0 : ℝ)).Countable :=
    (hD.union (Set.countable_range ((↑) : ℚ → ℝ))).mono hsubset
  let g : ℝ → Set.Ioi (0 : ℝ) := fun x => ⟨Real.exp x, Real.exp_pos x⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply Real.exp_injective
    exact Subtype.mk.inj hxy
  letI : Countable (Set.Ioi (0 : ℝ)) := hIoi.to_subtype
  have hc : Countable ℝ := hg.countable
  exfalso
  exact (not_countable_iff.mpr (inferInstance : Uncountable ℝ)) hc
