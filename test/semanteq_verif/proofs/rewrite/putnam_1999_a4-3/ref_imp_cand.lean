import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1999_a4_solution : ℝ := 9/32

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a4_assumed
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∑' m : ℕ, ∑' n : ℕ, (m^2 * n : ℝ) / ((3^m : ℝ) * ((n * 3^m : ℝ) + (m * 3^n : ℝ))) = 9 / 32 := by
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
  have hsupport : Function.support f ⊆ Set.range Nat.succ := by
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_cases hn0 : n = 0
    · subst n
      exact (hn hf0).elim
    · exact ⟨n - 1, Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn0)⟩
  have houter : (∑' m, f m) = ∑' m, g m := by
    rw [← Nat.succ_injective.tsum_eq hsupport]
    exact tsum_congr hfg
  have hg_nonneg : ∀ m, 0 ≤ g m := by
    intro m
    apply tsum_nonneg
    intro n
    positivity
  have hg_sum : HasSum g putnam_1999_a4_solution :=
    (hasSum_iff_tendsto_nat_of_nonneg hg_nonneg putnam_1999_a4_solution).2
      putnam_1999_a4_assumed
  change (∑' m, f m) = 9 / 32
  rw [houter, hg_sum.tsum_eq]
