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
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) := by
  let A : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  let B : ℕ → ℝ := fun m =>
    ∑' n : ℕ, (if m = 0 ∨ n = 0 then 0 else (m^2 * n : ℝ) / (3^m * (n * 3^m + m * 3^n)))
  have tsum_zero_shift (f : ℕ → ℝ) (hf0 : f 0 = 0) :
      ∑' n, f n = ∑' n, f (n + 1) := by
    by_cases hf : Summable f
    · rw [hf.tsum_eq_zero_add, hf0, zero_add]
    · have ht : ¬Summable (fun n => f (n + 1)) := by
        rwa [summable_nat_add_iff 1]
      rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable ht]
  have hBA (m : ℕ) : B (m + 1) = A m := by
    simp only [B, Nat.cast_add, Nat.cast_one]
    rw [tsum_zero_shift _ (by simp only [or_true, if_true])]
    apply tsum_congr
    intro n
    simp only [Nat.add_one_ne_zero, false_or, if_false, Nat.cast_add, Nat.cast_one]
  have hAssumed : ∑' m, B m = 9 / 32 := problem_statement_assumed
  have hB : Summable B := by
    -- non-rewrite step: a nonzero `tsum` cannot be Mathlib's nonsummable default value.
    apply Classical.byContradiction
    intro hn
    have hz : ∑' m, B m = 0 := tsum_eq_zero_of_not_summable hn
    have hval : (9 / 32 : ℝ) = 0 := by
      rw [← hz]
      exact hAssumed.symm
    exact (div_ne_zero (OfNat.ofNat_ne_zero 9) (OfNat.ofNat_ne_zero 32)) hval
  have hBshift : Summable (fun m => B (m + 1)) :=
    (summable_nat_add_iff 1).2 hB
  have hA : Summable A := (summable_congr hBA).1 hBshift
  have hB0 : B 0 = 0 := by
    simp only [B, true_or, if_true, tsum_zero]
  have hsumA : ∑' m, A m = 9 / 32 := by
    rw [hB.tsum_eq_zero_add, hB0, zero_add, tsum_congr hBA] at hAssumed
    exact hAssumed
  change Tendsto (fun i => ∑ m ∈ Finset.range i, A m) atTop (𝓝 (9 / 32))
  rw [← hsumA]
  exact hA.hasSum.tendsto_sum_nat
