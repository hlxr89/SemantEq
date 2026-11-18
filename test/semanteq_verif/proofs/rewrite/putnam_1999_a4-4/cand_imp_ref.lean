import Mathlib
open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

noncomputable def term (m n : ℕ) : ℝ :=
  if m = 0 ∨ n = 0 then 0 else ((m : ℝ)^2 * (n : ℝ)) / (((3 : ℝ)^m) * ((n : ℝ) * (3 : ℝ)^m + (m : ℝ) * (3 : ℝ)^n))

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∑' m : ℕ, ∑' n : ℕ, term m n = 9/32 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a4
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) := by
  let f : ℕ → ℝ := fun m => ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  have hshift : (fun m : ℕ => ∑' n : ℕ, term (m + 1) n) = f := by
    funext m
    apply tsum_eq_tsum_of_hasSum_iff_hasSum
    intro a
    have hterm : term (m + 1) = fun n : ℕ =>
        if n = 0 then 0 else ((m + 1 : ℕ) : ℝ)^2 * (n : ℝ) /
          ((3 : ℝ)^(m + 1) * ((n : ℝ) * (3 : ℝ)^(m + 1) + ((m + 1 : ℕ) : ℝ) * (3 : ℝ)^n)) := by
      funext n
      simp only [term, Nat.add_one_ne_zero, false_or]
    rw [hterm]
    have hs := (hasSum_nat_add_iff (g := a) (f := fun n : ℕ => term (m + 1) n) 1).symm
    rw [hterm] at hs
    simpa only [Nat.add_eq_zero_iff, one_ne_zero, and_false, or_false,
      false_or, true_or, if_false, if_true, Nat.cast_add, Nat.cast_one, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, add_zero] using hs
  have hcand_eq : (∑' m : ℕ, ∑' n : ℕ, term m n) = ∑' m : ℕ, f m := by
    apply tsum_eq_tsum_of_hasSum_iff_hasSum
    intro a
    rw [← hshift]
    simpa only [term, Nat.add_one_ne_zero, false_or, true_or, if_false, if_true,
      tsum_zero, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, add_zero] using
      (hasSum_nat_add_iff (f := fun m : ℕ => ∑' n : ℕ, term m n) 1).symm
  have hf_tsum : ∑' m : ℕ, f m = 9/32 :=
    hcand_eq.symm.trans problem_statement_assumed
  have hf_summable : Summable f := by
    have hf_ne : (∑' m : ℕ, f m) ≠ 0 := by
      rw [hf_tsum]
      positivity
    exact Classical.not_not.mp (mt tsum_eq_zero_of_not_summable hf_ne) -- non-rewrite step
  have hf_hasSum : HasSum f putnam_1999_a4_solution := by
    simpa only [putnam_1999_a4_solution, hf_tsum] using hf_summable.hasSum
  exact hf_hasSum.tendsto_sum_nat
