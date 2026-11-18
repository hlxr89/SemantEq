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
  let g : ℕ → (ℝ × ℝ → ℝ) := fun n p =>
    let N : ℝ := (n : ℝ) + 1
    let k := ⌊N * p.1⌋
    (1 - Int.fract (N * p.1)) * f ((k : ℝ) / N, p.2) +
      Int.fract (N * p.1) * f (((k : ℝ) + 1) / N, p.2)
  refine ⟨g, ?_, ?_⟩
  · intro n
    let N : ℝ := (n : ℝ) + 1
    have hN : 0 < N := by dsimp [N]; positivity
    let C : ℤ → Set (ℝ × ℝ) := fun k =>
      {p | (k : ℝ) ≤ N * p.1 ∧ N * p.1 ≤ (k : ℝ) + 1}
    have hC : LocallyFinite C := by
      intro p
      let t : Set (ℝ × ℝ) := {q | p.1 - 1 < q.1 ∧ q.1 < p.1 + 1}
      refine ⟨t, ?_, ?_⟩
      · apply IsOpen.mem_nhds
        · exact (isOpen_lt continuous_const continuous_fst).inter
            (isOpen_lt continuous_fst continuous_const)
        · change p.1 - 1 < p.1 ∧ p.1 < p.1 + 1
          constructor <;> linarith
      · refine (Set.finite_Icc (⌊N * (p.1 - 1)⌋ - 2) (⌈N * (p.1 + 1)⌉ + 2)).subset ?_
        intro k hk
        obtain ⟨q, hq, hqt⟩ := hk
        change (k : ℝ) ≤ N * q.1 ∧ N * q.1 ≤ (k : ℝ) + 1 at hq
        change p.1 - 1 < q.1 ∧ q.1 < p.1 + 1 at hqt
        have hlo : (N * (p.1 - 1) : ℝ) < (k : ℝ) + 1 := by nlinarith
        have hhi : (k : ℝ) < N * (p.1 + 1) := by nlinarith
        constructor
        · exact_mod_cast (show ((⌊N * (p.1 - 1)⌋ - 2 : ℤ) : ℝ) ≤ (k : ℝ) by
            have := Int.floor_le (N * (p.1 - 1))
            push_cast
            linarith)
        · have hkceil : k < ⌈N * (p.1 + 1)⌉ := Int.lt_ceil.2 hhi
          omega
    change Continuous (fun p : ℝ × ℝ =>
      (1 - Int.fract (N * p.1)) * f ((⌊N * p.1⌋ : ℝ) / N, p.2) +
        Int.fract (N * p.1) * f (((⌊N * p.1⌋ : ℝ) + 1) / N, p.2))
    apply hC.continuous
    · ext p
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨⌊N * p.1⌋, Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    · intro k
      exact (isClosed_le continuous_const (continuous_const.mul continuous_fst)).inter
        (isClosed_le (continuous_const.mul continuous_fst) continuous_const)
    · intro k
      have hc : Continuous (fun p : ℝ × ℝ =>
          (1 - (N * p.1 - (k : ℝ))) * f ((k : ℝ) / N, p.2) +
            (N * p.1 - (k : ℝ)) * f (((k : ℝ) + 1) / N, p.2)) := by
        have hz : Continuous (fun p : ℝ × ℝ => N * p.1) :=
          continuous_const.mul continuous_fst
        exact ((continuous_const.sub (hz.sub continuous_const)).mul
          ((hfconty ((k : ℝ) / N)).comp continuous_snd)).add
          ((hz.sub continuous_const).mul
            ((hfconty (((k : ℝ) + 1) / N)).comp continuous_snd))
      apply ContinuousOn.congr hc.continuousOn
      intro p hp
      change (k : ℝ) ≤ N * p.1 ∧ N * p.1 ≤ (k : ℝ) + 1 at hp
      rcases hp.2.eq_or_lt with heq | hlt
      · have heq' : N * p.1 = ((k + 1 : ℤ) : ℝ) := by norm_num at heq ⊢; linarith
        simp [heq', Int.fract]
      · have hfl : ⌊N * p.1⌋ = k := Int.floor_eq_iff.2 ⟨hp.1, hlt⟩
        simp only [Int.fract, hfl]
  · intro x y
    have ha : Tendsto (fun n : ℕ => (⌊((n : ℝ) + 1) * x⌋ : ℝ) / ((n : ℝ) + 1))
        atTop (nhds x) := by
      have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hlow : Tendsto (fun n : ℕ => x - 1 / ((n : ℝ) + 1)) atTop (nhds x) := by
        simpa using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (nhds x)).sub hzero
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (nhds x)) ?_ ?_
      · filter_upwards with n
        have hpos : 0 < (n : ℝ) + 1 := by positivity
        have hf := Int.lt_floor_add_one (((n : ℝ) + 1) * x)
        rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hpos]
        simpa [mul_comm] using hf.le
      · filter_upwards with n
        have hpos : 0 < (n : ℝ) + 1 := by positivity
        rw [div_le_iff₀ hpos]
        simpa [mul_comm] using Int.floor_le (((n : ℝ) + 1) * x)
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hb : Tendsto (fun n : ℕ => ((⌊((n : ℝ) + 1) * x⌋ : ℝ) + 1) /
        ((n : ℝ) + 1)) atTop (nhds x) := by
      simpa only [add_div, add_zero] using ha.add hzero
    have hA : Tendsto (fun n : ℕ => f (((⌊((n : ℝ) + 1) * x⌋ : ℝ) /
        ((n : ℝ) + 1)), y)) atTop (nhds (f (x, y))) := (hfcontx y).tendsto x |>.comp ha
    have hB : Tendsto (fun n : ℕ => f ((((⌊((n : ℝ) + 1) * x⌋ : ℝ) + 1) /
        ((n : ℝ) + 1)), y)) atTop (nhds (f (x, y))) := (hfcontx y).tendsto x |>.comp hb
    have hmin : Tendsto (fun n : ℕ => min
        (f (((⌊((n : ℝ) + 1) * x⌋ : ℝ) / ((n : ℝ) + 1)), y))
        (f ((((⌊((n : ℝ) + 1) * x⌋ : ℝ) + 1) / ((n : ℝ) + 1)), y)))
        atTop (nhds (f (x, y))) := by simpa using hA.min hB
    have hmax : Tendsto (fun n : ℕ => max
        (f (((⌊((n : ℝ) + 1) * x⌋ : ℝ) / ((n : ℝ) + 1)), y))
        (f ((((⌊((n : ℝ) + 1) * x⌋ : ℝ) + 1) / ((n : ℝ) + 1)), y)))
        atTop (nhds (f (x, y))) := by simpa using hA.max hB
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax
    · filter_upwards with n
      have ht0 : 0 ≤ Int.fract (((n : ℝ) + 1) * x) := Int.fract_nonneg _
      have ht1 : Int.fract (((n : ℝ) + 1) * x) ≤ 1 := (Int.fract_lt_one _).le
      dsimp only [g]
      rcases le_total (f (((⌊((n : ℝ) + 1) * x⌋ : ℝ) / ((n : ℝ) + 1)), y))
        (f ((((⌊((n : ℝ) + 1) * x⌋ : ℝ) + 1) / ((n : ℝ) + 1)), y)) with h | h
      · rw [min_eq_left h]
        nlinarith
      · rw [min_eq_right h]
        nlinarith
    · filter_upwards with n
      have ht0 : 0 ≤ Int.fract (((n : ℝ) + 1) * x) := Int.fract_nonneg _
      have ht1 : Int.fract (((n : ℝ) + 1) * x) ≤ 1 := (Int.fract_lt_one _).le
      dsimp only [g]
      rcases le_total (f (((⌊((n : ℝ) + 1) * x⌋ : ℝ) / ((n : ℝ) + 1)), y))
        (f ((((⌊((n : ℝ) + 1) * x⌋ : ℝ) + 1) / ((n : ℝ) + 1)), y)) with h | h
      · rw [max_eq_right h]
        nlinarith
      · rw [max_eq_left h]
        nlinarith
