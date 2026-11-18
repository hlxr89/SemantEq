import Mathlib

open Set Nat Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed
  (f : ℝ → ℝ → ℝ)
  (h1 : ∀ y, Continuous (fun x => f x y))
  (h2 : ∀ x, Continuous (fun y => f x y)) :
  ∃ (g : ℕ → ℝ → ℝ → ℝ),
    (∀ n, Continuous (g n)) ∧
    (∀ x y, Filter.Tendsto (fun n => g n x y) Filter.atTop (nhds (f x y))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1974_b4
(f : ℝ × ℝ → ℝ)
(hfcontx : ∀ y : ℝ, Continuous (fun x => f ⟨x, y⟩))
(hfconty : ∀ x : ℝ, Continuous (fun y => f ⟨x, y⟩))
: ∃ g : ℕ → (ℝ × ℝ → ℝ), (∀ n : ℕ, Continuous (g n)) ∧ (∀ x y : ℝ, Tendsto (fun n => g n ⟨x, y⟩) atTop (𝓝 (f ⟨x, y⟩))) := by
  let d : ℕ → ℝ := fun n => (n : ℝ) + 1
  let g : ℕ → ℝ × ℝ → ℝ := fun n p =>
    let t := d n * p.2
    let k := ⌊t⌋
    (1 - Int.fract t) * f ⟨p.1, (k : ℝ) / d n⟩ +
      Int.fract t * f ⟨p.1, ((k : ℝ) + 1) / d n⟩
  refine ⟨g, ?_, ?_⟩
  · intro n
    have hd : 0 < d n := by dsimp [d]; positivity
    let U : ℤ → Set ℝ := fun k => Icc (k : ℝ) (k + 1 : ℝ)
    have hU : LocallyFinite U := by
      intro x
      refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
      apply (Set.finite_Icc ⌊x - 2⌋ ⌈x + 1⌉).subset
      intro k hk
      rcases hk with ⟨z, ⟨hzk, hkz⟩, hzx⟩
      have hlo : x - 2 < (k : ℝ) := by linarith [hzx.1]
      have hhi : (k : ℝ) < x + 1 := by linarith [hzx.2]
      constructor
      · exact_mod_cast (Int.floor_le (x - 2)).trans hlo.le
      · exact_mod_cast hhi.le.trans (Int.le_ceil (x + 1))
    let S : ℤ → Set (ℝ × ℝ) := fun k => (fun p => d n * p.2) ⁻¹' U k
    have hS : LocallyFinite S :=
      hU.preimage_continuous (continuous_const.mul continuous_snd)
    apply hS.continuous
    · apply Set.eq_univ_of_forall
      intro p
      apply Set.mem_iUnion.2
      refine ⟨⌊d n * p.2⌋, ?_⟩
      exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    · intro k
      exact isClosed_Icc.preimage (continuous_const.mul continuous_snd)
    · intro k
      let e : ℝ × ℝ → ℝ := fun p =>
        (1 - (d n * p.2 - (k : ℝ))) * f ⟨p.1, (k : ℝ) / d n⟩ +
          (d n * p.2 - (k : ℝ)) * f ⟨p.1, ((k : ℝ) + 1) / d n⟩
      have he : Continuous e := by
        dsimp [e]
        exact (continuous_const.sub ((continuous_const.mul continuous_snd).sub continuous_const)).mul
          ((hfcontx _).comp continuous_fst) |>.add
          (((continuous_const.mul continuous_snd).sub continuous_const).mul
            ((hfcontx _).comp continuous_fst))
      apply he.continuousOn.congr
      intro p hp
      change g n p = e p
      dsimp [g, e]
      change d n * p.2 ∈ Icc (k : ℝ) (k + 1 : ℝ) at hp
      rcases lt_or_eq_of_le hp.2 with hlt | heq
      · have hk : ⌊d n * p.2⌋ = k := Int.floor_eq_iff.2 ⟨hp.1, by simpa using hlt⟩
        simp [Int.fract, hk]
      · have hk : ⌊d n * p.2⌋ = k + 1 := by
          rw [heq]
          norm_num
        rw [hk, heq]
        norm_num
  · intro x y
    let a : ℕ → ℝ := fun n => (⌊d n * y⌋ : ℝ) / d n
    let b : ℕ → ℝ := fun n => ((⌊d n * y⌋ : ℝ) + 1) / d n
    let r : ℕ → ℝ := fun n => Int.fract (d n * y)
    have ha : Tendsto a atTop (𝓝 y) := by
      rw [tendsto_iff_dist_tendsto_zero]
      apply squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) _
        (show Tendsto (fun n : ℕ => 1 / d n) atTop (𝓝 0) by
          simpa [d] using
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      exact Eventually.of_forall fun n => by
        have hd : 0 < d n := by dsimp [d]; positivity
        have hal : a n ≤ y := by
          apply (div_le_iff₀ hd).2
          simpa [mul_comm] using (Int.floor_le (d n * y))
        calc
          dist (a n) y = y - a n := by
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hal)]
            ring
          _ = r n / d n := by
            apply (eq_div_iff hd.ne').2
            have haa : a n * d n = (⌊d n * y⌋ : ℝ) := by
              dsimp [a]
              field_simp
            dsimp [r]
            linarith [Int.floor_add_fract (d n * y)]
          _ ≤ 1 / d n := by
            exact (div_le_div_iff_of_pos_right hd).2 (Int.fract_lt_one _).le
    have hb : Tendsto b atTop (𝓝 y) := by
      rw [tendsto_iff_dist_tendsto_zero]
      apply squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) _
        (show Tendsto (fun n : ℕ => 1 / d n) atTop (𝓝 0) by
          simpa [d] using
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      exact Eventually.of_forall fun n => by
        have hd : 0 < d n := by dsimp [d]; positivity
        have hbl : y ≤ b n := by
          apply (le_div_iff₀ hd).2
          simpa [mul_comm] using (Int.lt_floor_add_one (d n * y)).le
        calc
          dist (b n) y = b n - y := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hbl)]
          _ = (1 - r n) / d n := by
            apply (eq_div_iff hd.ne').2
            have hbb : b n * d n = (⌊d n * y⌋ : ℝ) + 1 := by
              dsimp [b]
              field_simp
            dsimp [r]
            linarith [Int.floor_add_fract (d n * y)]
          _ ≤ 1 / d n := by
            apply (div_le_div_iff_of_pos_right hd).2
            linarith [Int.fract_nonneg (d n * y)]
    have hA : Tendsto (fun n => f ⟨x, a n⟩) atTop (𝓝 (f ⟨x, y⟩)) :=
      (hfconty x).continuousAt.tendsto.comp ha
    have hB : Tendsto (fun n => f ⟨x, b n⟩) atTop (𝓝 (f ⟨x, y⟩)) :=
      (hfconty x).continuousAt.tendsto.comp hb
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) _
      (show Tendsto (fun n => dist (f ⟨x, a n⟩) (f ⟨x, y⟩) +
          dist (f ⟨x, b n⟩) (f ⟨x, y⟩)) atTop (𝓝 0) by
        simpa using ((tendsto_iff_dist_tendsto_zero.1 hA).add
          (tendsto_iff_dist_tendsto_zero.1 hB)))
    exact Eventually.of_forall fun n => by
      have hr0 : 0 ≤ r n := Int.fract_nonneg _
      have hr1 : r n ≤ 1 := (Int.fract_lt_one _).le
      change dist (g n ⟨x, y⟩) (f ⟨x, y⟩) ≤
        dist (f ⟨x, a n⟩) (f ⟨x, y⟩) + dist (f ⟨x, b n⟩) (f ⟨x, y⟩)
      dsimp [g]
      change |(1 - r n) * f ⟨x, a n⟩ + r n * f ⟨x, b n⟩ - f ⟨x, y⟩| ≤
        |f ⟨x, a n⟩ - f ⟨x, y⟩| + |f ⟨x, b n⟩ - f ⟨x, y⟩|
      calc
        |(1 - r n) * f ⟨x, a n⟩ + r n * f ⟨x, b n⟩ - f ⟨x, y⟩| =
            |(1 - r n) * (f ⟨x, a n⟩ - f ⟨x, y⟩) +
              r n * (f ⟨x, b n⟩ - f ⟨x, y⟩)| := by congr 1 <;> ring
        _ ≤ |(1 - r n) * (f ⟨x, a n⟩ - f ⟨x, y⟩)| +
              |r n * (f ⟨x, b n⟩ - f ⟨x, y⟩)| := abs_add_le _ _
        _ = (1 - r n) * |f ⟨x, a n⟩ - f ⟨x, y⟩| +
              r n * |f ⟨x, b n⟩ - f ⟨x, y⟩| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg]
                linarith
        _ ≤ |f ⟨x, a n⟩ - f ⟨x, y⟩| + |f ⟨x, b n⟩ - f ⟨x, y⟩| := by
              nlinarith [abs_nonneg (f ⟨x, a n⟩ - f ⟨x, y⟩),
                abs_nonneg (f ⟨x, b n⟩ - f ⟨x, y⟩)]
