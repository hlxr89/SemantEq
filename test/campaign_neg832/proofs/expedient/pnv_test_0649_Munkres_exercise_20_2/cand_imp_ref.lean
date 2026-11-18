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
  let e : (Σ _ : ℝ, ℝ) ≃ (ℝ ×ₗ ℝ) :=
    { toFun := fun p => toLex (p.1, p.2)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun p => by cases p; rfl
      right_inv := fun _ => rfl }
  have hc₀ (x : ℝ) : Continuous (fun y : ℝ => toLex (x, y)) := by
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
  have ho₀ (x : ℝ) : IsOpenMap (fun y : ℝ => toLex (x, y)) := by
    intro u hu
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨y, hy, rfl⟩
    rcases mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hy) with ⟨l, r, hyr, hlr⟩
    have hn : Ioo (toLex (x, l)) (toLex (x, r)) ∈ 𝓝 (toLex (x, y)) :=
      isOpen_Ioo.mem_nhds ⟨Prod.Lex.right x hyr.1, Prod.Lex.right x hyr.2⟩
    apply mem_of_superset hn
    intro q hq
    rcases Prod.lex_def.mp hq.1 with hxl | ⟨hxl, hql⟩
    · rcases Prod.lex_def.mp hq.2 with hxu | ⟨hxu, -⟩
      · exact (lt_asymm hxl hxu).elim
      · exact (hxl.ne hxu.symm).elim
    · rcases Prod.lex_def.mp hq.2 with hxu | ⟨hxu, hqu⟩
      · exact (hxu.ne hxl.symm).elim
      · refine ⟨q.2, hlr ⟨?_, ?_⟩, ?_⟩
        · simpa [hxl] using hql
        · simpa [hxu] using hqu
        · apply ofLex_inj.mpr
          exact Prod.ext hxl rfl
  have hc : Continuous (e : (Σ _ : ℝ, ℝ) → (ℝ ×ₗ ℝ)) := by
    rw [continuous_sigma_iff]
    exact fun x => by simpa [e] using hc₀ x
  have ho : IsOpenMap (e : (Σ _ : ℝ, ℝ) → (ℝ ×ₗ ℝ)) := by
    intro u hu
    rw [isOpen_sigma_iff] at hu
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨q, hq, rfl⟩
    have hs : IsOpen ((fun y : ℝ => (⟨q.1, y⟩ : Σ _ : ℝ, ℝ)) ⁻¹' u) := hu q.1
    have hm : toLex (q.1, q.2) ∈
        (fun y : ℝ => toLex (q.1, y)) ''
          ((fun y : ℝ => (⟨q.1, y⟩ : Σ _ : ℝ, ℝ)) ⁻¹' u) := ⟨q.2, hq, rfl⟩
    apply mem_of_superset ((ho₀ q.1 _ hs).mem_nhds hm)
    rintro z ⟨y, hy, rfl⟩
    exact ⟨⟨q.1, y⟩, hy, rfl⟩
  let h : (Σ _ : ℝ, ℝ) ≃ₜ (ℝ ×ₗ ℝ) := e.toHomeomorphOfContinuousOpen hc ho
  exact h.symm.isEmbedding.metrizableSpace
