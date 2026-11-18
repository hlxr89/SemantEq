import Mathlib
open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

noncomputable def term (m n : ℕ) : ℝ :=
  if m = 0 ∨ n = 0 then 0 else ((m : ℝ)^2 * (n : ℝ)) / (((3 : ℝ)^m) * ((n : ℝ) * (3 : ℝ)^m + (m : ℝ) * (3 : ℝ)^n))

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∑' m : ℕ, ∑' n : ℕ, term m n = 9/32 := by sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a4
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) := by
  have shift (f : ℕ → ℝ) (h0 : f 0 = 0) : (∑' n, f n) = ∑' n, f (n + 1) := by
    by_cases h : Summable f
    · simpa [h0] using (h.sum_add_tsum_nat_add 1).symm
    · have h' : ¬ Summable (fun n => f (n + 1)) := by
        simpa only [summable_nat_add_iff] using h
      rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable h']
  have bridge : (∑' m : ℕ, ∑' n : ℕ, term m n) =
      ∑' m : ℕ, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ) := by
    calc
      (∑' m : ℕ, ∑' n : ℕ, term m n) = ∑' m : ℕ, ∑' n : ℕ, term m (n + 1) := by
        apply tsum_congr
        intro m
        apply shift
        simp [term]
      _ = ∑' m : ℕ, ∑' n : ℕ, term (m + 1) (n + 1) := by
        apply shift
        simp [term]
      _ = _ := by
        apply tsum_congr
        intro m
        apply tsum_congr
        intro n
        simp [term]
  have heq : (∑' m : ℕ, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) = (9 / 32 : ℝ) := by
    rw [← bridge]
    exact problem_statement_assumed
  have hsum : Summable (fun m : ℕ => ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at heq
    norm_num at heq
  have hs := hsum.hasSum
  rw [heq] at hs
  exact hs.tendsto_sum_nat
