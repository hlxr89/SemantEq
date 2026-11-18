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
  letI : TopologicalSpace (ℝ ×ₗ ℝ) := Preorder.topology (ℝ ×ₗ ℝ)
  letI : OrderTopology (ℝ ×ₗ ℝ) := ⟨rfl⟩
  letI : MetrizableSpace (ℝ ×ₗ ℝ) := exercise_20_2_assumed
  let f : ℝ ↪o (ℝ ×ₗ ℝ) :=
    { toFun := fun y => toLex (0, y)
      inj' := by
        intro a b h
        simpa using congr_arg (fun z => (ofLex z).2) h
      map_rel_iff' := by
        intro a b
        simp [Prod.Lex.toLex_le_toLex] }
  have hconn : OrdConnected (Set.range f) := by
    constructor
    intro _ ha _ hb z hz
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    have hx : (ofLex z).1 = 0 := by
      have h₁ : (0 : ℝ) ≤ (ofLex z).1 :=
        (Prod.Lex.toLex_le_toLex'.1 (by simpa [f] using hz.1)).1
      have h₂ : (ofLex z).1 ≤ (0 : ℝ) :=
        (Prod.Lex.toLex_le_toLex'.1 (by simpa [f] using hz.2)).1
      by_contra h
      rcases lt_or_gt_of_ne h with hx | hx
      · exact (not_le_of_gt hx) h₁
      · exact (not_le_of_gt hx) h₂
    refine ⟨(ofLex z).2, ?_⟩
    apply ofLex.injective
    exact Prod.ext hx.symm rfl
  letI : MetrizableSpace ℝ := (f.isEmbedding_of_ordConnected hconn).metrizableSpace
  infer_instance
