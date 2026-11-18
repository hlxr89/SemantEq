import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∑' m : ℕ, ∑' n : ℕ, (if m = 0 ∨ n = 0 then 0 else (m^2 * n : ℝ) / (3^m * (n * 3^m + m * 3^n))) = 9/32 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a4
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) :=
by
  let a : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  let b : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (if m = 0 ∨ n = 0 then 0 else (m^2 * n : ℝ) / (3^m * (n * 3^m + m * 3^n)))
  have tsum_zero_shift (f : ℕ → ℝ) (hf : f 0 = 0) :
      (∑' n : ℕ, f n) = ∑' n : ℕ, f (n + 1) := by
    by_cases hs : Summable f
    · simpa [hf] using hs.tsum_eq_zero_add
    · have hs' : ¬ Summable (fun n : ℕ => f (n + 1)) := by
        intro h
        exact hs ((summable_nat_add_iff 1).mp h)
      rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable hs']
  have hb_shift (m : ℕ) : b (m + 1) = a m := by
    dsimp [b]
    rw [tsum_zero_shift _ (by simp)]
    apply tsum_congr
    intro n
    simp [a]
  have hb0 : b 0 = 0 := by simp [b]
  have hba : (∑' m : ℕ, b m) = ∑' m : ℕ, a m := by
    rw [tsum_zero_shift b hb0]
    exact tsum_congr hb_shift
  have hb_tsum : (∑' m : ℕ, b m) = 9 / 32 := by
    simpa [b] using problem_statement_assumed
  have hb_ne : (∑' m : ℕ, b m) ≠ 0 := by
    rw [hb_tsum]
    norm_num
  have hb_sum : Summable b := by
    by_contra h
    exact hb_ne (tsum_eq_zero_of_not_summable h)
  have ha_sum : Summable a := by
    have hshift : Summable (fun m : ℕ => b (m + 1)) :=
      (summable_nat_add_iff 1).2 hb_sum
    simpa only [hb_shift] using hshift
  have ha_tsum : (∑' m : ℕ, a m) = putnam_1999_a4_solution := by
    rw [← hba, hb_tsum]
  simpa [a, ha_tsum] using ha_sum.tendsto_sum_tsum_nat
