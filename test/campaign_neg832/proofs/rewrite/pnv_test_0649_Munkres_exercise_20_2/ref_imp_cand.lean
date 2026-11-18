import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_20_2_assumed
  [TopologicalSpace (ℝ ×ₗ ℝ)] [OrderTopology (ℝ ×ₗ ℝ)]
  : MetrizableSpace (ℝ ×ₗ ℝ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : MetrizableSpace (Prod ℝ ℝ) := by
  letI : TopologicalSpace (ℝ ×ₗ ℝ) :=
    Preorder.topology (α := ℝ ×ₗ ℝ)
  letI : OrderTopology (ℝ ×ₗ ℝ) := ⟨rfl⟩
  letI : MetrizableSpace (ℝ ×ₗ ℝ) := exercise_20_2_assumed
  have hc : Continuous (fun y : ℝ => toLex ((0 : ℝ), y)) := by
    rw [OrderTopology.continuous_iff]
    intro a
    constructor
    · rw [show (fun y : ℝ => toLex ((0 : ℝ), y)) ⁻¹' Ioi a =
          {y : ℝ | a.1 < (0 : ℝ) ∨ a.1 = 0 ∧ a.2 < y} by
        ext y
        exact Prod.lex_def]
      by_cases h : a.1 < 0
      · simp [h]
      · by_cases hx : a.1 = 0
        · simpa [h, hx] using isOpen_Ioi
        · simp [h, hx]
    · rw [show (fun y : ℝ => toLex ((0 : ℝ), y)) ⁻¹' Iio a =
          {y : ℝ | (0 : ℝ) < a.1 ∨ 0 = a.1 ∧ y < a.2} by
        ext y
        exact Prod.lex_def]
      by_cases h : 0 < a.1
      · simp [h]
      · by_cases hx : 0 = a.1
        · simpa [h, hx] using isOpen_Iio
        · simp [h, hx]
  have ho : IsOpenMap (fun y : ℝ => toLex ((0 : ℝ), y)) := by
    intro u hu
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨y, hy, rfl⟩
    rcases mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hy) with ⟨l, r, hyr, hlr⟩
    have hn : Ioo (toLex ((0 : ℝ), l)) (toLex ((0 : ℝ), r)) ∈
        𝓝 (toLex ((0 : ℝ), y)) :=
      isOpen_Ioo.mem_nhds
        ⟨Prod.Lex.right (0 : ℝ) hyr.1, Prod.Lex.right (0 : ℝ) hyr.2⟩
    apply mem_of_superset hn
    intro q hq
    rcases Prod.lex_def.mp hq.1 with hxl | ⟨hxl, hql⟩
    · rcases Prod.lex_def.mp hq.2 with hxu | ⟨hxu, hqu⟩
      · exact (lt_asymm hxl hxu).elim
      · exact (hxl.ne hxu.symm).elim
    · rcases Prod.lex_def.mp hq.2 with hxu | ⟨hxu, hqu⟩
      · exact (hxu.ne hxl.symm).elim
      · refine ⟨q.2, hlr ⟨?_, ?_⟩, ?_⟩
        · simpa [hxl] using hql
        · simpa [hxu] using hqu
        · apply ofLex_inj.mpr
          exact Prod.ext hxl rfl
  have he : Topology.IsEmbedding (fun y : ℝ => toLex ((0 : ℝ), y)) :=
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hc
      (fun _ _ h => congrArg (fun p => p.2) (ofLex_inj.mp h)) ho).isEmbedding
  letI : MetrizableSpace ℝ := he.metrizableSpace
  exact metrizableSpace_prod
