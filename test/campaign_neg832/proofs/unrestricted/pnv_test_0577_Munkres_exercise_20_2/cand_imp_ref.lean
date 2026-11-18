import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [PolishSpace X] : MetrizableSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_20_2
  [TopologicalSpace (ℝ ×ₗ ℝ)] [OrderTopology (ℝ ×ₗ ℝ)]
  : MetrizableSpace (ℝ ×ₗ ℝ) := by
  let vertical : ℝ → ℝ ↪o (ℝ ×ₗ ℝ) := fun x =>
    { toFun := fun y => toLex (x, y)
      inj' := fun _ _ h => by simpa using congrArg (fun z => (ofLex z).2) h
      map_rel_iff' := by simp [Prod.Lex.toLex_le_toLex] }
  have hconn (x : ℝ) : OrdConnected (range (vertical x)) := by
    rw [ordConnected_iff]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ z hz
    have hlow : x ≤ (ofLex z).1 := by
      rcases Prod.Lex.le_iff.mp hz.1 with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    have hupp : (ofLex z).1 ≤ x := by
      rcases Prod.Lex.le_iff.mp hz.2 with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    refine ⟨(ofLex z).2, ?_⟩
    apply ofLex.injective
    change (x, (ofLex z).2) = ofLex z
    exact Prod.ext (le_antisymm hlow hupp) rfl
  have hopen (x : ℝ) : IsOpen (range (vertical x)) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨y, rfl⟩
    rw [mem_nhds_iff_exists_Ioo_subset]
    refine ⟨toLex (x, y - 1), toLex (x, y + 1), ?_, ?_⟩
    · change toLex (x, y - 1) < toLex (x, y) ∧ toLex (x, y) < toLex (x, y + 1)
      simp [Prod.Lex.toLex_lt_toLex]
    · exact Ioo_subset_Icc_self.trans
        ((hconn x).out (mem_range_self (y - 1)) (mem_range_self (y + 1)))
  have hemb (x : ℝ) : Topology.IsOpenEmbedding (vertical x) :=
    ⟨(vertical x).isEmbedding_of_ordConnected (hconn x), hopen x⟩
  let e : (ℝ ×ₗ ℝ) ≃ (Σ _ : ℝ, ℝ) :=
    { toFun := fun z => ⟨(ofLex z).1, (ofLex z).2⟩
      invFun := fun z => toLex (z.1, z.2)
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }
  let g : (Σ _ : ℝ, ℝ) → (ℝ ×ₗ ℝ) := fun z => toLex (z.1, z.2)
  have hg_cont : Continuous g := continuous_sigma (fun x => (hemb x).continuous)
  have hg_open : IsOpenMap g := isOpenMap_sigma.2 (fun x => (hemb x).isOpenMap)
  let h := e.symm.toHomeomorphOfContinuousOpen hg_cont hg_open
  exact h.symm.isEmbedding.metrizableSpace
