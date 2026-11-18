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
    rcases Metric.uniformContinuous_iff.mp hf 1 zero_lt_one with ⟨δ, hδ, hloc⟩
    let S : ℝ → Set ℝ := fun r ↦ {y | ∃ s t : ℝ, |s - t| ≤ max r 0 ∧ y = |f s - f t|}
    have Sne (r : ℝ) : (S r).Nonempty := by
      refine ⟨0, 0, 0, ?_, by simp⟩
      simp
    have Sbdd (r : ℝ) : BddAbove (S r) := by
      obtain ⟨N : ℕ, hN⟩ := Archimedean.arch (max r 0) (half_pos hδ)
      refine ⟨N, ?_⟩
      rintro y ⟨s, t, hst, rfl⟩
      wlog hle : s ≤ t generalizing s t
      · rw [abs_sub_comm]
        exact this t s (by simpa [abs_sub_comm] using hst) (le_of_not_ge hle)
      let p : ℕ → Icc s t := Set.Icc.addNSMul hle (δ / 2)
      have hp0 : p 0 = ⟨s, le_rfl, hle⟩ := by
        apply Subtype.ext
        exact Set.Icc.addNSMul_zero hle
      have hpN : p N = ⟨t, hle, le_rfl⟩ := by
        apply Subtype.ext
        simp only [p, Set.Icc.addNSMul, Set.coe_projIcc]
        rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hst
        have ht : t ≤ s + N • (δ / 2) := by
          calc
            t ≤ s + max r 0 := by linarith
            _ ≤ s + N • (δ / 2) := by simpa [add_comm] using add_le_add_left hN s
        rw [min_eq_left ht, max_eq_right hle]
      have hchain : ∀ n ≤ N, |f s - f (p n)| ≤ n := by
        intro n hn
        induction n with
        | zero => simp [hp0]
        | succ n ih =>
          have hnN : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
          have hstep : |(p n : ℝ) - p (n + 1)| < δ := by
            calc
              |(p n : ℝ) - p (n + 1)| ≤
                  |(s + n • (δ / 2)) - (s + (n + 1) • (δ / 2))| :=
                Set.abs_projIcc_sub_projIcc hle
              _ = δ / 2 := by
                rw [show s + n • (δ / 2) - (s + (n + 1) • (δ / 2)) = -(δ / 2) by
                  ring]
                rw [abs_neg, abs_of_nonneg (div_nonneg hδ.le (by norm_num))]
              _ < δ := half_lt_self hδ
          calc
            |f s - f (p (n + 1))| ≤ |f s - f (p n)| + |f (p n) - f (p (n + 1))| := abs_sub_le _ _ _
            _ ≤ n + 1 := by
              have := hloc hstep
              exact add_le_add (ih hnN) this.le
            _ = (n + 1 : ℕ) := by norm_num
      simpa [hpN] using hchain N le_rfl
    let μ : ℝ → ℝ := fun r ↦ r + sSup (S r)
    have hSmono {x y : ℝ} (hxy : x ≤ y) : S x ⊆ S y := by
      rintro z ⟨s, t, hst, rfl⟩
      exact ⟨s, t, hst.trans (max_le_max_right 0 hxy), rfl⟩
    have hsSupmono {x y : ℝ} (hxy : x ≤ y) : sSup (S x) ≤ sSup (S y) :=
      csSup_le (Sne x) fun z hz ↦ le_csSup (Sbdd y) (hSmono hxy hz)
    refine ⟨μ, ?_, ?_, ?_⟩
    · intro x y hxy
      exact add_lt_add_of_lt_of_le hxy (hsSupmono hxy.le)
    · rw [Metric.tendsto_nhds_nhds]
      intro ε hε
      rcases Metric.uniformContinuous_iff.mp hf (ε / 4) (by positivity) with ⟨d, hd, hdloc⟩
      refine ⟨min (ε / 4) d, by positivity, ?_⟩
      intro r hr
      rw [Real.dist_eq, sub_zero] at hr
      have hrabs : |r| < ε / 4 := hr.trans_le (min_le_left _ _)
      have hrd : max r 0 < d := by
        apply lt_of_le_of_lt (max_le (le_abs_self r) (abs_nonneg r))
        exact hr.trans_le (min_le_right _ _)
      have hsup0 : 0 ≤ sSup (S r) := le_csSup (Sbdd r) (by exact ⟨0, 0, by simp, by simp⟩)
      have hsup : sSup (S r) ≤ ε / 4 := by
        apply csSup_le (Sne r)
        rintro z ⟨s, t, hst, rfl⟩
        exact (hdloc (hst.trans_lt hrd)).le
      rw [Real.dist_eq]
      dsimp [μ]
      rw [sub_zero]
      calc
        |r + sSup (S r)| ≤ |r| + |sSup (S r)| := abs_add_le _ _
        _ = |r| + sSup (S r) := by rw [abs_of_nonneg hsup0]
        _ < ε := by linarith
    · intro s t
      dsimp [μ]
      have hmem : |f s - f t| ∈ S |s - t| := ⟨s, t, by simp, rfl⟩
      have hle := le_csSup (Sbdd |s - t|) hmem
      linarith [abs_nonneg (s - t)]
  · rintro ⟨μ, hμ, hμ0, hbound⟩
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    rw [Metric.tendsto_nhds_nhds] at hμ0
    rcases hμ0 ε hε with ⟨δ, hδ, hclose⟩
    refine ⟨δ / 2, by positivity, ?_⟩
    intro s t hst
    have hμdist : μ |s - t| < μ (δ / 2) := hμ (by simpa [Real.dist_eq] using hst)
    have harg : dist (δ / 2) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      linarith
    have hμsmall : |μ (δ / 2)| < ε := by
      simpa [Real.dist_eq] using hclose harg
    rw [Real.dist_eq]
    calc
      |f s - f t| ≤ μ |s - t| := hbound s t
      _ < μ (δ / 2) := hμdist
      _ ≤ |μ (δ / 2)| := le_abs_self _
      _ < ε := hμsmall
