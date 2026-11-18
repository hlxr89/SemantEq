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
  let v (x y : ℝ) : ℝ ×ₗ ℝ := toLex (x, y)
  have hv_mono (x : ℝ) : StrictMono (v x) := by
    intro a b hab
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inr ⟨rfl, hab⟩
  have hv_ord (x : ℝ) : OrdConnected (range (v x)) := by
    rw [ordConnected_def]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ z ⟨haz, hzb⟩
    have hxz : x ≤ (ofLex z).1 := (Prod.Lex.le_iff'.mp haz).1
    have hzx : (ofLex z).1 ≤ x := (Prod.Lex.le_iff'.mp hzb).1
    refine ⟨(ofLex z).2, ?_⟩
    simp only [v]
    rw [show x = (ofLex z).1 from le_antisymm hxz hzx]
    exact toLex_ofLex z
  have hv_open (x : ℝ) : IsOpen (range (v x)) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨y, rfl⟩
    apply mem_of_superset
      (Ioo_mem_nhds (hv_mono x (sub_lt_self y zero_lt_one))
        (hv_mono x (lt_add_of_pos_right y zero_lt_one)))
    intro z hz
    have hxz : x ≤ (ofLex z).1 := (Prod.Lex.lt_iff'.mp hz.1).1
    have hzx : (ofLex z).1 ≤ x := (Prod.Lex.lt_iff'.mp hz.2).1
    refine ⟨(ofLex z).2, ?_⟩
    simp only [v]
    rw [show x = (ofLex z).1 from le_antisymm hxz hzx]
    exact toLex_ofLex z
  have hv_emb (x : ℝ) : Topology.IsEmbedding (v x) :=
    (hv_mono x).isEmbedding_of_ordConnected (hv_ord x)
  have hv_openEmb (x : ℝ) : Topology.IsOpenEmbedding (v x) :=
    ⟨hv_emb x, hv_open x⟩
  let e : (Σ _ : ℝ, ℝ) ≃ (ℝ ×ₗ ℝ) :=
    { toFun := fun p => v p.1 p.2
      invFun := fun p => ⟨(ofLex p).1, (ofLex p).2⟩
      left_inv := by rintro ⟨x, y⟩; rfl
      right_inv := by intro p; exact toLex_ofLex p }
  have he_cont : Continuous e := by
    apply continuous_sigma
    intro x
    simpa only [e] using (hv_emb x).continuous
  have he_open : IsOpenMap e := by
    rw [isOpenMap_sigma]
    intro x
    simpa only [e] using (hv_openEmb x).isOpenMap
  let h := e.toHomeomorphOfContinuousOpen he_cont he_open
  exact h.symm.isEmbedding.metrizableSpace
