import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_15a_assumed (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℝ → ℝ} : UniformContinuous f ↔ ∃ μ : ℝ → ℝ, StrictMono μ ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧ ∀ s t, |f s - f t| ≤ μ (|s - t|) := by
  constructor
  · intro hf
    rcases (Metric.uniformContinuous_iff.mp hf) 1 zero_lt_one with ⟨d, hd, hlocal⟩
    have hbounded : ∀ r : ℝ, BddAbove {y : ℝ | ∃ s t : ℝ, |s - t| ≤ max r 0 ∧ y = |f s - f t|} := by
      intro r
      obtain ⟨n, hn⟩ := exists_nat_gt ((max r 0) / d)
      have hn0 : 0 < n := by
        have hnonneg : 0 ≤ (max r 0) / d := div_nonneg (le_max_right _ _) hd.le
        have : (0 : ℝ) < n := lt_of_le_of_lt hnonneg hn
        exact_mod_cast this
      refine ⟨(n : ℝ), ?_⟩
      rintro y ⟨s, t, hst, rfl⟩
      let p : ℕ → ℝ := fun i ↦ s + (i : ℝ) / n * (t - s)
      have hstep : ∀ i < n, |p i - p (i + 1)| < d := by
        intro i hi
        have hnreal : (0 : ℝ) < n := by exact_mod_cast hn0
        have hratio : max r 0 < (n : ℝ) * d := by
          apply (div_lt_iff₀ hd).mp at hn
          simpa [mul_comm] using hn
        calc
          |p i - p (i + 1)| = |t - s| / n := by
            have heq : p i - p (i + 1) = -(t - s) / (n : ℝ) := by
              dsimp [p]
              push_cast
              field_simp
              ring
            rw [heq, abs_div, abs_neg, abs_of_pos hnreal]
          _ = |s - t| / n := by rw [abs_sub_comm]
          _ ≤ max r 0 / n := (div_le_div_iff_of_pos_right hnreal).2 hst
          _ < d := (div_lt_iff₀ hnreal).2 (by simpa [mul_comm] using hratio)
      have hterms : ∀ i ∈ Finset.range n, |f (p i) - f (p (i + 1))| ≤ 1 := by
        intro i hi
        exact (hlocal (by simpa [Real.dist_eq] using hstep i (Finset.mem_range.mp hi))).le
      calc
        |f s - f t| = |∑ i ∈ Finset.range n, (f (p i) - f (p (i + 1)))| := by
          rw [Finset.sum_range_sub']
          simp [p, hn0.ne']
        _ ≤ ∑ i ∈ Finset.range n, |f (p i) - f (p (i + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum hterms
        _ = n := by simp
    let S : ℝ → Set ℝ := fun r ↦ {y : ℝ | ∃ s t : ℝ, |s - t| ≤ max r 0 ∧ y = |f s - f t|}
    let ω : ℝ → ℝ := fun r ↦ sSup (S r)
    have hSne : ∀ r, (S r).Nonempty := by
      intro r
      refine ⟨0, 0, 0, ?_, by simp⟩
      simp
    have hω_nonneg : ∀ r, 0 ≤ ω r := by
      intro r
      apply le_csSup (hbounded r)
      exact ⟨0, 0, by simp, by simp⟩
    have hω_mono : Monotone ω := by
      intro r q hrq
      apply csSup_le (hSne r)
      intro y hy
      apply le_csSup (hbounded q)
      rcases hy with ⟨s, t, hst, rfl⟩
      exact ⟨s, t, hst.trans (max_le_max hrq le_rfl), rfl⟩
    have hω_bound : ∀ s t : ℝ, |f s - f t| ≤ ω |s - t| := by
      intro s t
      apply le_csSup (hbounded |s - t|)
      exact ⟨s, t, by simp, rfl⟩
    have hω0 : Tendsto ω (𝓝 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      rcases (Metric.uniformContinuous_iff.mp hf) (ε / 2) (half_pos hε) with ⟨δ, hδ, hδf⟩
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with r hr
      rw [Metric.mem_ball, Real.dist_eq] at hr
      rw [Real.dist_eq]
      have hrmax : max r 0 < δ := by
        rw [max_lt_iff]
        exact ⟨lt_of_le_of_lt (le_abs_self r) (by simpa using hr), hδ⟩
      have htop : ω r ≤ ε / 2 := by
        apply csSup_le (hSne r)
        rintro y ⟨s, t, hst, rfl⟩
        exact (hδf (by simpa [Real.dist_eq] using hst.trans_lt hrmax)).le
      simpa [abs_of_nonneg (hω_nonneg r)] using lt_of_le_of_lt htop (half_lt_self hε)
    refine ⟨fun x ↦ x + ω x, ?_, ?_, ?_⟩
    · intro x y hxy
      exact add_lt_add_of_lt_of_le hxy (hω_mono hxy.le)
    · simpa using tendsto_id.add hω0
    · intro s t
      exact (hω_bound s t).trans (le_add_of_nonneg_left (abs_nonneg (s - t)))
  · rintro ⟨μ, hmono, hμ0, hbound⟩
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    have hev : Filter.Eventually (fun x : ℝ ↦ μ x < ε) (𝓝 0) :=
      (tendsto_order.1 hμ0).2 ε hε
    rcases (Metric.eventually_nhds_iff.mp hev) with ⟨δ, hδ, hδμ⟩
    refine ⟨δ, hδ, ?_⟩
    intro s t hst
    rw [Real.dist_eq] at hst ⊢
    exact lt_of_le_of_lt (hbound s t)
      (hδμ (by simpa [Real.dist_eq, abs_sub_comm] using hst))
