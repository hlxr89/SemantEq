import Mathlib
open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

noncomputable def term (m n : ℕ) : ℝ :=
  if m = 0 ∨ n = 0 then 0 else ((m : ℝ)^2 * (n : ℝ)) / (((3 : ℝ)^m) * ((n : ℝ) * (3 : ℝ)^m + (m : ℝ) * (3 : ℝ)^n))

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a4_assumed
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) :=
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  ∑' m : ℕ, ∑' n : ℕ, term m n = 9/32 := by
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
  have hs : HasSum
      (fun m : ℕ => ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ))
      putnam_1999_a4_solution := by
    have hnonneg : ∀ m : ℕ, 0 ≤ ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ) := by
      intro m
      apply tsum_nonneg
      intro n
      positivity
    exact (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2 putnam_1999_a4_assumed
  calc
    (∑' m : ℕ, ∑' n : ℕ, term m n) =
        ∑' m : ℕ, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ) := bridge
    _ = putnam_1999_a4_solution := hs.tsum_eq
    _ = 9/32 := rfl
