import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_63a_assumed (p : ℝ) (f : ℕ → ℝ) (hp : p > 1)
  (h : f = λ (k : ℕ) => (1 : ℝ) / (k * (log k) ^ p)) :
  ∃ l, Tendsto f atTop (𝓝 l) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {p : ℝ} (hp : 1 < p) : Summable fun k : ℕ => 1 / (k * log k ^ p) := by
  let F : ℝ → ℝ := fun x => 1 / (x * (log x) ^ p)
  let G : ℝ → ℝ := fun x => (log x) ^ (1 - p) / (1 - p)
  have hF_nonneg : ∀ n : ℕ, 0 ≤ F n := by
    intro n
    dsimp [F]
    positivity
  have hG_deriv : ∀ x : ℝ, 1 < x → HasDerivAt G (F x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
    have hl : 0 < log x := log_pos hx
    have hpne : 1 - p ≠ 0 := by linarith
    dsimp [G, F]
    convert ((Real.hasDerivAt_log hx0).rpow_const (Or.inl hl.ne')).div_const (1 - p) using 1
    field_simp [hpne]
    rw [show 1 - p - 1 = -p by ring]
    rw [Real.rpow_neg (le_of_lt hl)]
    field_simp
  have hF_anti (n : ℕ) : AntitoneOn F (Set.Icc (2 : ℝ) n) := by
    intro x hx y hy hxy
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
    have hypos : 0 < y := hxpos.trans_le hxy
    have hlx : 0 < log x := log_pos (lt_of_lt_of_le (by norm_num) hx.1)
    have hlog : log x ≤ log y := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hxpos) (Set.mem_Ioi.mpr hypos) hxy
    have hrpow : (log x) ^ p ≤ (log y) ^ p :=
      Real.rpow_le_rpow hlx.le hlog (by linarith)
    dsimp [F]
    apply one_div_le_one_div_of_le
    · exact mul_pos hxpos (Real.rpow_pos_of_pos hlx p)
    · exact mul_le_mul hxy hrpow (Real.rpow_nonneg hlx.le p) hypos.le
  apply summable_of_sum_range_le hF_nonneg
    (c := (∑ i ∈ Finset.range 3, F i) - G 2)
  intro n
  by_cases hn : n < 3
  · have hsub : Finset.range n ⊆ Finset.range 3 := Finset.range_mono hn.le
    calc
      ∑ i ∈ Finset.range n, F i ≤ ∑ i ∈ Finset.range 3, F i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hF_nonneg i)
      _ ≤ (∑ i ∈ Finset.range 3, F i) - G 2 := by
        have hG2 : G 2 ≤ 0 := by
          dsimp [G]
          exact div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (log_nonneg (by norm_num)) _)
            (by linarith)
        linarith
  · have hn3 : 3 ≤ n := by omega
    have hn2 : 2 ≤ n - 1 := by omega
    have hint : IntervalIntegrable F MeasureTheory.volume 2 (n - 1 : ℕ) := by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le (mod_cast hn2)] at hx
      have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx.1
      have hx0 : x ≠ 0 := by positivity
      have hl0 : log x ≠ 0 := (log_pos hx1).ne'
      have hden : x * log x ^ p ≠ 0 := mul_ne_zero hx0
        ((Real.rpow_ne_zero (log_pos hx1).le (by linarith)).mpr hl0)
      dsimp [F]
      exact (continuousAt_const.div
        (continuousAt_id.mul ((Real.continuousAt_log hx0).rpow_const (Or.inl hl0))) hden).continuousWithinAt
    have hintegral : (∫ x in (2 : ℝ)..(n - 1 : ℕ), F x) = G (n - 1 : ℕ) - G 2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        apply hG_deriv x
        rw [Set.uIcc_of_le (mod_cast hn2)] at hx
        exact lt_of_lt_of_le (by norm_num) hx.1
      · exact hint
    have htail : (∑ i ∈ Finset.Ico 3 n, F i) ≤ G (n - 1 : ℕ) - G 2 := by
      rw [← hintegral]
      convert (hF_anti (n - 1)).sum_le_integral_Ico hn2 using 1
      rw [show n = 1 + (n - 1) by omega]
      symm
      simpa [add_comm] using
        (Finset.sum_Ico_add (fun i : ℕ => F i) 2 (n - 1) 1)
    have hGn : G (n - 1 : ℕ) ≤ 0 := by
      dsimp [G]
      apply div_nonpos_of_nonneg_of_nonpos
      · exact Real.rpow_nonneg (log_nonneg (by norm_num; omega)) _
      · linarith
    rw [← Finset.sum_range_add_sum_Ico (fun i : ℕ => F i) hn3]
    linarith
