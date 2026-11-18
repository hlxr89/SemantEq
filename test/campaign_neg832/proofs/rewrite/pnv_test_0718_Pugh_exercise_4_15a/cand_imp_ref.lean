import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) : UniformContinuousOn f (Set.Icc a b) ↔ ∃ (M : ℝ → ℝ), ContinuousOn f (Set.Icc a b) ∧ (∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ ⦃x y⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → abs (x - y) < ε → abs (f x - f y) ≤ M ε) ∧ Tendsto M (𝓝[>] 0) (𝓝 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  constructor
  · intro hf
    let S : ℝ → Set ℝ := fun x =>
      {z | ∃ s t : Icc a b, z = |f s - f t| ∧ |(s : ℝ) - (t : ℝ)| ≤ x}
    let ω : ℝ → ℝ := fun x => if 0 < x then sSup (S x) else 0
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (isCompact_range hf.continuous).isBounded
    have hS_bdd : ∀ x, BddAbove (S x) := by
      intro x
      refine ⟨C, ?_⟩
      intro z hz
      obtain ⟨s, t, rfl, hst⟩ := hz
      simpa [Real.dist_eq] using hC (mem_range_self s) (mem_range_self t)
    have hS_nonempty : ∀ {x : ℝ}, 0 < x → (S x).Nonempty := by
      intro x hx
      let p : Icc a b := ⟨a, left_mem_Icc.mpr hab⟩
      refine ⟨0, p, p, by simp, ?_⟩
      simpa using hx.le
    have hω_nonneg : ∀ x, 0 ≤ ω x := by
      intro x
      by_cases hx : 0 < x
      · change 0 ≤ (if 0 < x then sSup (S x) else 0)
        rw [if_pos hx]
        apply le_csSup (hS_bdd x)
        let p : Icc a b := ⟨a, left_mem_Icc.mpr hab⟩
        exact ⟨p, p, by simp, by simpa using hx.le⟩
      · simp [ω, hx]
    have hω_mono : MonotoneOn ω (Ioi 0) := by
      intro x hx y hy hxy
      have hx' : 0 < x := hx
      have hy' : 0 < y := hy
      change (if 0 < x then sSup (S x) else 0) ≤
        (if 0 < y then sSup (S y) else 0)
      rw [if_pos hx', if_pos hy']
      apply csSup_le_csSup (hS_bdd y) (hS_nonempty hx')
      intro z hz
      obtain ⟨s, t, hval, hdist⟩ := hz
      exact ⟨s, t, hval, hdist.trans hxy⟩
    have hω_lim : Tendsto ω (𝓝 0) (𝓝 0) := by
      rw [tendsto_order]
      constructor
      · intro c hc
        exact Filter.Eventually.of_forall fun x => hc.trans_le (hω_nonneg x)
      · intro ε hε
        have hε2 : 0 < ε / 2 := half_pos hε
        obtain ⟨δ, hδ, huc⟩ := (Metric.uniformContinuous_iff.mp hf) (ε / 2) hε2
        apply Metric.eventually_nhds_iff.mpr
        refine ⟨δ, hδ, ?_⟩
        intro x hx
        by_cases hx0 : 0 < x
        · change (if 0 < x then sSup (S x) else 0) < ε
          rw [if_pos hx0]
          apply lt_of_le_of_lt (csSup_le (hS_nonempty hx0) ?_) (half_lt_self hε)
          intro z hz
          obtain ⟨s, t, rfl, hst⟩ := hz
          have hxd : x < δ := by
            simpa [Real.dist_eq, abs_of_pos hx0] using hx
          have hdist : dist s t < δ := by
            simpa [Real.dist_eq] using hst.trans_lt hxd
          exact le_of_lt (by simpa [Real.dist_eq] using huc hdist)
        · simp [ω, hx0, hε]
    let μ : ℝ → ℝ := fun x => x + ω x
    refine ⟨μ, ?_⟩
    intro x
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hx
      exact add_pos_of_pos_of_nonneg hx (hω_nonneg x)
    · intro u hu v hv huv
      exact add_lt_add_of_lt_of_le huv (hω_mono hu hv huv.le)
    · change Tendsto (fun x : ℝ => x + ω x) (𝓝 0) (𝓝 0)
      simpa using tendsto_id.add hω_lim
    · intro s t
      let d : ℝ := |(s : ℝ) - (t : ℝ)|
      by_cases hd : d = 0
      · have hst : s = t := by
          apply Subtype.ext
          exact sub_eq_zero.mp (abs_eq_zero.mp hd)
        subst t
        simp [μ, d, ω]
      · have hd0 : 0 < d := (abs_pos.mpr (sub_ne_zero.mpr fun h => hd (by simpa [d, h])))
        have hmem : |f s - f t| ∈ S d := ⟨s, t, rfl, le_rfl⟩
        have hle : |f s - f t| ≤ ω d := by
          change |f s - f t| ≤ (if 0 < d then sSup (S d) else 0)
          rw [if_pos hd0]
          exact le_csSup (hS_bdd d) hmem
        exact hle.trans (le_add_of_nonneg_left hd0.le)
  · rintro ⟨μ, hμ⟩
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    have hev : ∀ᶠ x : ℝ in 𝓝 0, μ x < ε :=
      (tendsto_order.mp (hμ 0 |>.2.2.1)).2 ε hε
    obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨δ, hδ, ?_⟩
    intro s t hst
    have hμδ : μ (dist s t) < ε := hsmall (by simpa [Real.dist_eq] using hst)
    exact lt_of_le_of_lt (by simpa [Real.dist_eq] using hμ 0 |>.2.2.2 s t) hμδ
