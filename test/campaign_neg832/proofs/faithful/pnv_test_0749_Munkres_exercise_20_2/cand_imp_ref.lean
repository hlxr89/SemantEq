import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : MetrizableSpace (Prod.{0,0} ℝ ℝ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_20_2
  [TopologicalSpace (ℝ ×ₗ ℝ)] [OrderTopology (ℝ ×ₗ ℝ)]
  : MetrizableSpace (ℝ ×ₗ ℝ) := by
  have hreal : MetrizableSpace ℝ := by
    letI : TopologicalSpace (ℝ × ℝ) := instTopologicalSpaceProd
    letI : MetrizableSpace (ℝ × ℝ) := dummy_assumed
    exact (isEmbedding_prodMkRight (0 : ℝ)).metrizableSpace
  have hsigma : MetrizableSpace (Σ _ : ℝ, ℝ) := by
    letI : MetrizableSpace ℝ := hreal
    letI : MetricSpace ℝ := TopologicalSpace.metrizableSpaceMetric ℝ
    letI : MetricSpace (Σ _ : ℝ, ℝ) := Metric.Sigma.metricSpace
    infer_instance
  let φ (a : ℝ) (b : ℝ) : ℝ ×ₗ ℝ := toLex (a, b)
  have hφ (a : ℝ) : Topology.IsOpenEmbedding (φ a) := by
    have hm : StrictMono (φ a) := fun _ _ h => Prod.Lex.right a h
    have hc : Set.OrdConnected (Set.range (φ a)) := by
      constructor
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ z hz
      have hza : (ofLex z).1 = a := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have : z < φ a x := Prod.Lex.left (ofLex z).2 x hlt
          exact not_lt_of_ge hz.1 this
        · have : φ a y < z := Prod.Lex.left y (ofLex z).2 hgt
          exact not_lt_of_ge hz.2 this
      refine ⟨(ofLex z).2, ?_⟩
      have hp : (a, (ofLex z).2) = ofLex z := by ext <;> simp [hza]
      exact (congrArg toLex hp).trans (toLex_ofLex z)
    refine ⟨hm.isEmbedding_of_ordConnected hc, ?_⟩
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨b, rfl⟩
    apply mem_of_superset (Ioo_mem_nhds (Prod.Lex.right a (sub_lt_self b zero_lt_one))
      (Prod.Lex.right a (lt_add_of_pos_right b zero_lt_one)))
    intro z hz
    have hza : (ofLex z).1 = a := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : z < φ a (b - 1) := Prod.Lex.left (ofLex z).2 (b - 1) hlt
        exact not_lt_of_ge hz.1.le this
      · have : φ a (b + 1) < z := Prod.Lex.left (b + 1) (ofLex z).2 hgt
        exact not_lt_of_ge hz.2.le this
    refine ⟨(ofLex z).2, ?_⟩
    have hp : (a, (ofLex z).2) = ofLex z := by ext <;> simp [hza]
    exact (congrArg toLex hp).trans (toLex_ofLex z)
  let e : (Σ _ : ℝ, ℝ) ≃ (ℝ ×ₗ ℝ) :=
    { toFun := fun z => φ z.1 z.2
      invFun := fun z => ⟨(ofLex z).1, (ofLex z).2⟩
      left_inv := by rintro ⟨a, b⟩; rfl
      right_inv := by intro z; exact toLex_ofLex z }
  have hecont : Continuous e := continuous_sigma_iff.2 fun a => (hφ a).continuous
  have heopen : IsOpenMap e := isOpenMap_sigma.2 fun a => (hφ a).isOpenMap
  letI : MetrizableSpace (Σ _ : ℝ, ℝ) := hsigma
  exact (e.toHomeomorphOfContinuousOpen hecont heopen).symm.isEmbedding.metrizableSpace
