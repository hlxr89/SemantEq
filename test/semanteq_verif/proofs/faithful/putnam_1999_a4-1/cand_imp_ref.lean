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
  let A : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  let B : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (if m = 0 ∨ n = 0 then 0 else (m^2 * n : ℝ) / (3^m * (n * 3^m + m * 3^n)))
  have hB_tsum : ∑' m, B m = putnam_1999_a4_solution := by
    simpa [B, putnam_1999_a4_solution] using problem_statement_assumed
  have hB_summable : Summable B := by
    by_contra h
    have hz : ∑' m, B m = 0 := tsum_eq_zero_of_not_summable h
    rw [hB_tsum] at hz
    norm_num [putnam_1999_a4_solution] at hz
  have hB : HasSum B putnam_1999_a4_solution := by
    rw [← hB_tsum]
    exact hB_summable.hasSum
  have hshift : ∀ m, B (m + 1) = A m := by
    intro m
    apply tsum_eq_tsum_of_hasSum_iff_hasSum
    intro a
    simpa [A, B] using (hasSum_nat_add_iff (g := a) (f := fun n : ℕ =>
      if m + 1 = 0 ∨ n = 0 then 0
      else ((↑(m + 1) : ℝ)^2 * n) /
        (3^(m + 1) * (n * 3^(m + 1) + (↑(m + 1) : ℝ) * 3^n))) 1).symm
  have hshifted : HasSum (fun m => B (m + 1)) putnam_1999_a4_solution := by
    apply (hasSum_nat_add_iff (f := B) 1).2
    simpa [B] using hB
  have hA : HasSum A putnam_1999_a4_solution := by
    simpa only [hshift] using hshifted
  exact hA.tendsto_sum_nat
