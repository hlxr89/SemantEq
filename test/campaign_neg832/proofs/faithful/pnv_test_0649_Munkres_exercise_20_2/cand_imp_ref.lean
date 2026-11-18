import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : MetrizableSpace (Prod ℝ ℝ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_20_2
  [TopologicalSpace (ℝ ×ₗ ℝ)] [OrderTopology (ℝ ×ₗ ℝ)]
  : MetrizableSpace (ℝ ×ₗ ℝ) := by
  letI : MetrizableSpace (Prod ℝ ℝ) := dummy_assumed
  letI : MetrizableSpace ℝ := (isEmbedding_prodMkRight (0 : ℝ)).metrizableSpace
  letI : MetricSpace ℝ := TopologicalSpace.metrizableSpaceMetric ℝ
  letI : MetricSpace (Σ _ : ℝ, ℝ) := Metric.Sigma.metricSpace
  let e : (ℝ ×ₗ ℝ) ≃ (Σ _ : ℝ, ℝ) :=
    { toFun := fun z => ⟨(ofLex z).1, (ofLex z).2⟩
      invFun := fun z => toLex (z.1, z.2)
      left_inv := by intro z; simp
      right_inv := by rintro ⟨x, y⟩; rfl }
  have hfiber (x : ℝ) : Topology.IsEmbedding (fun y : ℝ => toLex (x, y)) := by
    let f : ℝ ↪o (ℝ ×ₗ ℝ) :=
      { toFun := fun y => toLex (x, y)
        inj' := by
          intro a b h
          simpa using congr_arg (fun z => (ofLex z).2) h
        map_rel_iff' := by
          intro a b
          simp [Prod.Lex.toLex_le_toLex] }
    apply f.isEmbedding_of_ordConnected
    constructor
    intro _ ha _ hb z hz
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    have hx : (ofLex z).1 = x := by
      have h₁ : x ≤ (ofLex z).1 :=
        (Prod.Lex.toLex_le_toLex'.1 (by simpa [f] using hz.1)).1
      have h₂ : (ofLex z).1 ≤ x :=
        (Prod.Lex.toLex_le_toLex'.1 (by simpa [f] using hz.2)).1
      exact h₂.antisymm h₁
    refine ⟨(ofLex z).2, ?_⟩
    apply ofLex.injective
    exact Prod.ext hx.symm rfl
  have he_cont : Continuous e := by
    rw [continuous_def]
    intro s hs
    apply isOpen_iff_forall_mem_open.2
    intro z hz
    have hsx : IsOpen (Sigma.mk (ofLex z).1 ⁻¹' s) := isOpen_sigma_iff.1 hs _
    have hzy : (ofLex z).2 ∈ Sigma.mk (ofLex z).1 ⁻¹' s := by simpa [e] using hz
    obtain ⟨a, b, hab, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (hsx.mem_nhds hzy)
    refine ⟨Ioo (toLex ((ofLex z).1, a)) (toLex ((ofLex z).1, b)), ?_,
      isOpen_Ioo, ?_⟩
    · intro w hw
      have h₁ := Prod.Lex.toLex_lt_toLex'.1 (by simpa using hw.1)
      have h₂ := Prod.Lex.toLex_lt_toLex'.1 (by simpa using hw.2)
      have hx : (ofLex w).1 = (ofLex z).1 := h₂.1.antisymm h₁.1
      have ha : a < (ofLex w).2 := h₁.2 hx.symm
      have hb : (ofLex w).2 < b := h₂.2 hx
      have := hsub ⟨ha, hb⟩
      simpa [e, hx] using this
    · constructor
      · have hleft :
            toLex ((ofLex z).1, a) < toLex ((ofLex z).1, (ofLex z).2) :=
          Prod.Lex.toLex_lt_toLex'.2 ⟨le_rfl, fun _ => hab.1⟩
        simpa using hleft
      · have hright :
            toLex ((ofLex z).1, (ofLex z).2) < toLex ((ofLex z).1, b) :=
          Prod.Lex.toLex_lt_toLex'.2 ⟨le_rfl, fun _ => hab.2⟩
        simpa using hright
  have he_symm_cont : Continuous e.symm := by
    rw [continuous_def]
    intro s hs
    apply isOpen_sigma_iff.2
    intro x
    simpa [e] using (hs.preimage (hfiber x).continuous)
  exact (Homeomorph.mk e he_cont he_symm_cont).isEmbedding.metrizableSpace
