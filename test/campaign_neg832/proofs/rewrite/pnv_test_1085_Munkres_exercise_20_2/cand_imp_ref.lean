import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : MetrizableSpace (Prod.{0, 0} ℝ ℝ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_20_2
  [TopologicalSpace (ℝ ×ₗ ℝ)] [OrderTopology (ℝ ×ₗ ℝ)]
  : MetrizableSpace (ℝ ×ₗ ℝ) := by
  letI : MetrizableSpace (Prod.{0, 0} ℝ ℝ) := dummy_assumed
  -- non-rewrite step
  have hR : MetrizableSpace ℝ :=
    (isEmbedding_prodMkRight (0 : ℝ)).metrizableSpace
  letI : MetrizableSpace ℝ := hR
  let f (a : ℝ) : ℝ ↪o (ℝ ×ₗ ℝ) :=
    { toFun := fun y => toLex (a, y)
      inj' := by
        intro x y h
        exact congrArg (fun p => (ofLex p).2) h
      map_rel_iff' := by
        intro x y
        change toLex (a, x) ≤ toLex (a, y) ↔ x ≤ y
        rw [Prod.Lex.toLex_le_toLex]
        simp only [lt_irrefl, false_or, true_and] }
  have hf (a : ℝ) : OrdConnected (Set.range (f a)) := by
    rw [ordConnected_iff_uIcc_subset]
    intro x hx y hy z hz
    rcases hx with ⟨b, rfl⟩
    rcases hy with ⟨c, rfl⟩
    refine ⟨z.2, ?_⟩
    apply toLex_inj.mpr
    apply Prod.ext
    · rw [mem_uIcc] at hz
      rcases hz with hz | hz
      · exact le_antisymm
          (by simpa only [f] using Prod.Lex.monotone_fst (f a b) z hz.1)
          (by simpa only [f] using Prod.Lex.monotone_fst z (f a c) hz.2)
      · exact le_antisymm
          (by simpa only [f] using Prod.Lex.monotone_fst (f a c) z hz.1)
          (by simpa only [f] using Prod.Lex.monotone_fst z (f a b) hz.2)
    · rfl
  have hopen (a : ℝ) : IsOpen (Set.range (f a)) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases hz with ⟨y, rfl⟩
    refine mem_of_superset
      (Ioo_mem_nhds (a := toLex (a, y - 1)) (b := toLex (a, y + 1)) ?_ ?_) ?_
    · change toLex (a, y - 1) < toLex (a, y)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨rfl, sub_lt_self y zero_lt_one⟩
    · change toLex (a, y) < toLex (a, y + 1)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨rfl, lt_add_of_pos_right y zero_lt_one⟩
    · intro z hz
      refine ⟨z.2, ?_⟩
      apply toLex_inj.mpr
      apply Prod.ext
      · exact le_antisymm
          (by simpa only using Prod.Lex.monotone_fst (toLex (a, y - 1)) z hz.1.le)
          (by simpa only using Prod.Lex.monotone_fst z (toLex (a, y + 1)) hz.2.le)
      · rfl
  let e : (Σ _ : ℝ, ℝ) ≃ (ℝ ×ₗ ℝ) :=
    { toFun := fun p => toLex (p.1, p.2)
      invFun := fun p => ⟨(ofLex p).1, (ofLex p).2⟩
      left_inv := by intro p; cases p; rfl
      right_inv := by intro p; rfl }
  have hecont : Continuous e := by
    apply continuous_sigma
    intro a
    exact ((f a).isEmbedding_of_ordConnected (hf a)).continuous
  have heopen : IsOpenMap e := by
    rw [isOpenMap_sigma]
    intro a
    have ha : Topology.IsOpenEmbedding (f a) :=
      ⟨(f a).isEmbedding_of_ordConnected (hf a), hopen a⟩
    exact ha.isOpenMap
  exact (e.toHomeomorphOfContinuousOpen hecont heopen).symm.isEmbedding.metrizableSpace
