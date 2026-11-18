import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), (∀ (ε : ℝ), ε > 0 → μ ε > 0) ∧ (∀ (ε : ℝ), ε > 0 → ∀ (x y : X), dist x y < μ ε → dist (f x) (f y) < ε) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  constructor
  · intro hf
    obtain ⟨η, hηpos, hηmap⟩ := (dummy_assumed f).mp hf
    let A : ℝ → Set ℝ := fun r =>
      {z | ∃ s t : Icc a b, |(s : ℝ) - (t : ℝ)| ≤ r ∧ z = |f s - f t|}
    let ω : ℝ → ℝ := fun r => sSup (A r)
    let μ : ℝ → ℝ := fun r => r + ω r
    let q : (Icc a b × Icc a b) → ℝ := fun p => |f p.1 - f p.2|
    have hqcont : Continuous q := by
      dsimp [q]
      have hfcont : Continuous f := hf.continuous
      fun_prop
    have hqbound : BddAbove (q '' (Set.univ : Set (Icc a b × Icc a b))) :=
      isCompact_univ.bddAbove_image hqcont.continuousOn
    have hAbdd (r : ℝ) : BddAbove (A r) := by
      apply hqbound.mono
      rintro z ⟨s, t, _, rfl⟩
      exact ⟨(s, t), Set.mem_univ _, rfl⟩
    let p : Icc a b := ⟨a, le_rfl, hab⟩
    have hAzero (r : ℝ) (hr : 0 ≤ r) : 0 ∈ A r := by
      exact ⟨p, p, by simpa, by simp⟩
    have hAnonempty (r : ℝ) (hr : 0 ≤ r) : (A r).Nonempty :=
      ⟨0, hAzero r hr⟩
    have hω_nonneg (r : ℝ) (hr : 0 ≤ r) : 0 ≤ ω r :=
      le_csSup (hAbdd r) (hAzero r hr)
    have hω_mono {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : ω r ≤ ω s := by
      apply csSup_le (hAnonempty r hr)
      intro z hz
      apply le_csSup (hAbdd s)
      rcases hz with ⟨x, y, hxy, rfl⟩
      exact ⟨x, y, hxy.trans hrs, rfl⟩
    refine ⟨μ, fun x => ?_⟩
    constructor
    · intro hx
      exact add_pos_of_pos_of_nonneg hx (hω_nonneg x hx.le)
    constructor
    · intro x hx y hy hxy
      exact add_lt_add_of_lt_of_le hxy (hω_mono hx.le hxy.le)
    constructor
    · rw [Metric.tendsto_nhds]
      intro ε hε
      have he2 : 0 < ε / 2 := half_pos hε
      let d := min (η (ε / 2)) (ε / 2)
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨d, (lt_min_iff).2 ⟨hηpos _ he2, he2⟩, ?_⟩
      intro r hr
      have har : |r| < d := by simpa [Real.dist_eq] using hr
      by_cases hr0 : 0 ≤ r
      · have hrη : r < η (ε / 2) :=
          lt_of_le_of_lt (le_abs_self r) (har.trans_le (min_le_left _ _))
        have hωle : ω r ≤ ε / 2 := by
          apply csSup_le (hAnonempty r hr0)
          rintro z ⟨s, t, hst, rfl⟩
          have hdist : dist s t < η (ε / 2) := by
            simpa [Real.dist_eq] using lt_of_le_of_lt hst hrη
          exact (hηmap _ he2 s t hdist).le
        have hrhalf : r < ε / 2 :=
          lt_of_le_of_lt (le_abs_self r) (har.trans_le (min_le_right _ _))
        have hμ0 : 0 ≤ μ r := add_nonneg hr0 (hω_nonneg r hr0)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hμ0]
        change r + ω r < ε
        linarith
      · have hrneg : r < 0 := lt_of_not_ge hr0
        have hAempty : A r = ∅ := by
          ext z
          constructor
          · rintro ⟨s, t, hst, _⟩
            exact (not_le_of_gt hrneg) (abs_nonneg _ |>.trans hst)
          · simp
        have hωzero : ω r = 0 := by simp [ω, hAempty]
        rw [Real.dist_eq, sub_zero, show μ r = r by simp [μ, hωzero]]
        exact har.trans (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε))
    · intro s t
      have hmem : |f s - f t| ∈ A |(s : ℝ) - (t : ℝ)| :=
        ⟨s, t, le_rfl, rfl⟩
      have hleω : |f s - f t| ≤ ω |(s : ℝ) - (t : ℝ)| :=
        le_csSup (hAbdd _) hmem
      exact hleω.trans (le_add_of_nonneg_left (abs_nonneg _))
  · rintro ⟨μ, hμ⟩
    apply (dummy_assumed f).mpr
    let η : ℝ → ℝ := fun ε =>
      if hε : ε > 0 then
        (Classical.choose (Metric.eventually_nhds_iff.mp
          ((Metric.tendsto_nhds.mp (hμ 0).2.2.1) ε hε))) / 2
      else 1
    refine ⟨η, ?_, ?_⟩
    · intro ε hε
      let ρ := Classical.choose (Metric.eventually_nhds_iff.mp
        ((Metric.tendsto_nhds.mp (hμ 0).2.2.1) ε hε))
      have hρ : 0 < ρ := (Classical.choose_spec (Metric.eventually_nhds_iff.mp
        ((Metric.tendsto_nhds.mp (hμ 0).2.2.1) ε hε))).1
      rw [show η ε = ρ / 2 by simp [η, hε, ρ]]
      exact half_pos hρ
    · intro ε hε s t hst
      have hspec := Classical.choose_spec (Metric.eventually_nhds_iff.mp
        ((Metric.tendsto_nhds.mp (hμ 0).2.2.1) ε hε))
      let ρ := Classical.choose (Metric.eventually_nhds_iff.mp
        ((Metric.tendsto_nhds.mp (hμ 0).2.2.1) ε hε))
      have hρ : 0 < ρ := hspec.1
      have hηeq : η ε = ρ / 2 := by simp [η, hε, ρ]
      have hdist : |(s : ℝ) - (t : ℝ)| < ρ / 2 := by
        simpa [hηeq, Real.dist_eq] using hst
      by_cases heq : s = t
      · subst t
        simpa using hε
      · have hdpos : 0 < |(s : ℝ) - (t : ℝ)| :=
          abs_pos.mpr (sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr heq))
        have hμlt : μ |(s : ℝ) - (t : ℝ)| < μ (ρ / 2) :=
          (hμ 0).2.1 hdpos (half_pos hρ) hdist
        have hρnear : dist (ρ / 2) 0 < ρ := by
          rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hρ)]
          linarith
        have hμρ : |μ (ρ / 2)| < ε := by
          simpa [Real.dist_eq] using hspec.2 hρnear
        have hbound := (hμ |(s : ℝ) - (t : ℝ)|).2.2.2 s t
        have hμρpos : 0 < μ (ρ / 2) := (hμ (ρ / 2)).1 (half_pos hρ)
        simpa [Real.dist_eq] using hbound.trans_lt (hμlt.trans (lt_of_le_of_lt (le_abs_self _) hμρ))
