import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a4_assumed
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∑' m : ℕ, ∑' n : ℕ, (m^2 * n : ℝ) / ((3^m : ℝ) * ((n * 3^m : ℝ) + (m * 3^n : ℝ))) = 9 / 32 := by
  let a : ℕ → ℕ → ℝ := fun m n =>
    (m^2 * n : ℝ) / ((3^m : ℝ) * ((n * 3^m : ℝ) + (m * 3^n : ℝ)))
  let b : ℕ → ℕ → ℝ := fun m n =>
    (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  let A : ℕ → ℝ := fun m => ∑' n, a m n
  let B : ℕ → ℝ := fun m => ∑' n, b m n
  have shift_tsum (f : ℕ → ℝ) (h0 : f 0 = 0) :
      (∑' n, f n) = ∑' n, f (n + 1) := by
    by_cases hf : Summable f
    · rw [hf.tsum_eq_zero_add, h0, zero_add]
    · have htail : ¬ Summable (fun n => f (n + 1)) := by
        simpa only [summable_nat_add_iff 1] using hf
      rw [tsum_eq_zero_of_not_summable hf,
        tsum_eq_zero_of_not_summable htail]
  have hab (m n : ℕ) : a (m + 1) (n + 1) = b m n := by
    simp only [a, b, Nat.cast_add, Nat.cast_one]
  have hA0 : A 0 = 0 := by
    simp [A, a]
  have hAB (m : ℕ) : A (m + 1) = B m := by
    dsimp only [A, B]
    rw [shift_tsum (a (m + 1))]
    · exact tsum_congr (hab m)
    · simp [a]
  have hB_nonneg (m : ℕ) : 0 ≤ B m := by
    dsimp only [B]
    exact tsum_nonneg fun n => by positivity
  have hHasB : HasSum B putnam_1999_a4_solution := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hB_nonneg]
    simpa only [B, b] using putnam_1999_a4_assumed
  calc
    (∑' m : ℕ, ∑' n : ℕ, (m^2 * n : ℝ) /
        ((3^m : ℝ) * ((n * 3^m : ℝ) + (m * 3^n : ℝ)))) = ∑' m, A m := by rfl
    _ = ∑' m, A (m + 1) := shift_tsum A hA0
    _ = ∑' m, B m := tsum_congr hAB
    _ = putnam_1999_a4_solution := hHasB.tsum_eq
    _ = 9 / 32 := rfl
