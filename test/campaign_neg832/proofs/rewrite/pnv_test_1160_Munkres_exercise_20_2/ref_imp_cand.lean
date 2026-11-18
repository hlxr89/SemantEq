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
theorem dummy : MetrizableSpace (ℝ × ℝ) := by
  letI : TopologicalSpace (ℝ ×ₗ ℝ) := Preorder.topology (ℝ ×ₗ ℝ)
  letI : OrderTopology (ℝ ×ₗ ℝ) := ⟨rfl⟩
  letI : MetrizableSpace (ℝ ×ₗ ℝ) := exercise_20_2_assumed
  let e : (Σ _ : ℝ, ℝ) ≃ (ℝ ×ₗ ℝ) :=
    { toFun := fun p => toLex (p.1, p.2)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun p => by cases p; rfl
      right_inv := fun _ => rfl }
  have hc : Continuous (e : (Σ _ : ℝ, ℝ) → (ℝ ×ₗ ℝ)) := by
    rw [continuous_sigma_iff]
    intro x
    change Continuous (fun y : ℝ => toLex (x, y))
    rw [OrderTopology.continuous_iff]
    intro a
    constructor
    · rw [show (fun y : ℝ => toLex (x, y)) ⁻¹' Ioi a =
          {y : ℝ | a.1 < x ∨ a.1 = x ∧ a.2 < y} by
        ext y
        exact Prod.lex_def]
      by_cases h : a.1 < x
      · simp [h]
      · by_cases hx : a.1 = x
        · simpa [h, hx] using isOpen_Ioi
        · simp [h, hx]
    · rw [show (fun y : ℝ => toLex (x, y)) ⁻¹' Iio a =
          {y : ℝ | x < a.1 ∨ x = a.1 ∧ y < a.2} by
        ext y
        exact Prod.lex_def]
      by_cases h : x < a.1
      · simp [h]
      · by_cases hx : x = a.1
        · simpa [h, hx] using isOpen_Iio
        · simp [h, hx]
  have ho : IsOpenMap (e : (Σ _ : ℝ, ℝ) → (ℝ ×ₗ ℝ)) := by
    intro u hu
    rw [isOpen_sigma_iff] at hu
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨q, hq, rfl⟩
    have hs : IsOpen ((fun y : ℝ => (⟨q.1, y⟩ : Σ _ : ℝ, ℝ)) ⁻¹' u) := hu q.1
    have hv : IsOpenMap (fun y : ℝ => toLex (q.1, y)) := by
      intro v hv
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨y, hy, rfl⟩
      rcases mem_nhds_iff_exists_Ioo_subset.mp (hv.mem_nhds hy) with ⟨l, r, hyr, hlr⟩
      have hn : Ioo (toLex (q.1, l)) (toLex (q.1, r)) ∈ 𝓝 (toLex (q.1, y)) :=
        isOpen_Ioo.mem_nhds ⟨Prod.Lex.right q.1 hyr.1, Prod.Lex.right q.1 hyr.2⟩
      apply mem_of_superset hn
      intro z hz
      rcases Prod.lex_def.mp hz.1 with hxl | ⟨hxl, hzl⟩
      · rcases Prod.lex_def.mp hz.2 with hxu | ⟨hxu, hzu⟩
        · exact (lt_asymm hxl hxu).elim
        · exact (hxl.ne hxu.symm).elim
      · rcases Prod.lex_def.mp hz.2 with hxu | ⟨hxu, hzu⟩
        · exact (hxu.ne hxl.symm).elim
        · refine ⟨z.2, hlr ⟨?_, ?_⟩, ?_⟩
          · simpa [hxl] using hzl
          · simpa [hxu] using hzu
          · apply ofLex_inj.mpr
            exact Prod.ext hxl rfl
    have hm : toLex (q.1, q.2) ∈
        (fun y : ℝ => toLex (q.1, y)) ''
          ((fun y : ℝ => (⟨q.1, y⟩ : Σ _ : ℝ, ℝ)) ⁻¹' u) := ⟨q.2, hq, rfl⟩
    apply mem_of_superset ((hv _ hs).mem_nhds hm)
    rintro z ⟨y, hy, rfl⟩
    exact ⟨⟨q.1, y⟩, hy, rfl⟩
  let h : (Σ _ : ℝ, ℝ) ≃ₜ (ℝ ×ₗ ℝ) := e.toHomeomorphOfContinuousOpen hc ho
  letI : MetrizableSpace (Σ _ : ℝ, ℝ) := h.isEmbedding.metrizableSpace
  letI : MetrizableSpace ℝ :=
    (Topology.IsEmbedding.sigmaMk (ι := ℝ) (σ := fun _ : ℝ => ℝ)
      (i := (0 : ℝ))).metrizableSpace
  exact inferInstance
