import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∑' m : ℕ, ∑' n : ℕ, (m^2 * n : ℝ) / ((3^m : ℝ) * ((n * 3^m : ℝ) + (m * 3^n : ℝ))) = 9 / 32 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a4
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) := by
  let f : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (m^2 * n : ℝ) /
      ((3^m : ℝ) * ((n * 3^m : ℝ) + (m * 3^n : ℝ)))
  let g : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) *
      ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  have hfg : ∀ m, f (m + 1) = g m := by
    intro m
    let q : ℕ → ℝ := fun n => ( ((m + 1 : ℕ)^2 * n : ℕ) : ℝ) /
      ((3^(m + 1) : ℝ) * ((n * 3^(m + 1) : ℝ) + ((m + 1) * 3^n : ℝ)))
    have hq0 : q 0 = 0 := by
      simp only [q, mul_zero, Nat.cast_zero, zero_mul, zero_add, zero_div]
    have hq_support : Function.support q ⊆ Set.range Nat.succ := by
      intro n hn
      simp only [Function.mem_support, ne_eq] at hn
      by_cases hn0 : n = 0
      · subst n
        exact (hn hq0).elim
      · exact ⟨n - 1, Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn0)⟩
    have hq := Nat.succ_injective.tsum_eq hq_support
    simpa only [f, g, q, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_pow] using hq.symm
  have hf0 : f 0 = 0 := by
    simp only [f, pow_two, zero_mul, Nat.cast_zero, zero_div, tsum_zero]
  have hf_tsum : (∑' m, f m) = putnam_1999_a4_solution := by
    exact problem_statement_assumed
  have hf_ne : (∑' m, f m) ≠ 0 := by
    rw [hf_tsum]
    dsimp only [putnam_1999_a4_solution]
    positivity
  have hf_summable : Summable f := by
    -- non-rewrite step
    exact Classical.not_not.mp (mt tsum_eq_zero_of_not_summable hf_ne)
  have hf_sum : HasSum f putnam_1999_a4_solution := by
    rw [← hf_tsum]
    exact hf_summable.hasSum
  have hshift : HasSum (fun m => f (m + 1)) putnam_1999_a4_solution := by
    rw [hasSum_nat_add_iff 1]
    simpa only [Finset.sum_range_one, hf0, add_zero] using hf_sum
  have hg_sum : HasSum g putnam_1999_a4_solution := by
    exact hshift.congr_fun (fun m => (hfg m).symm)
  exact hg_sum.tendsto_sum_nat
