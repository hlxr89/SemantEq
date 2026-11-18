import Mathlib

open Real

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1986_a3_solution : ℝ := Real.pi / 2

-- ===== assumed statement (antecedent) =====
theorem putnam_1986_a3_assumed
(cot : ℝ → ℝ)
(fcot : cot = fun θ ↦ cos θ / sin θ)
(arccot : ℝ → ℝ)
(harccot : ∀ t : ℝ, t ≥ 0 → arccot t ∈ Set.Ioc 0 (Real.pi / 2) ∧ cot (arccot t) = t)
: (∑' n : ℕ, arccot (n ^ 2 + n + 1) = putnam_1986_a3_solution) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : ∑' n : ℕ, Real.arctan (1 / ((n : ℝ)^2 + (n : ℝ) + 1)) = π / 2 := by
  have hterm : ∀ n : ℕ, Real.arctan (1 / ((n : ℝ)^2 + (n : ℝ) + 1)) =
      Real.arctan (n + 1) - Real.arctan n := by
    intro n
    have hd : 0 < (n : ℝ)^2 + (n : ℝ) + 1 := by positivity
    have hq : (n : ℝ) * (1 / ((n : ℝ)^2 + (n : ℝ) + 1)) < 1 := by
      rw [mul_one_div]
      exact (div_lt_one hd).mpr (by nlinarith)
    have h := Real.arctan_add (x := (n : ℝ))
      (y := 1 / ((n : ℝ)^2 + (n : ℝ) + 1)) hq
    rw [show ((n : ℝ) + 1 / ((n : ℝ)^2 + (n : ℝ) + 1)) /
        (1 - (n : ℝ) * (1 / ((n : ℝ)^2 + (n : ℝ) + 1))) = n + 1 by
          apply (div_eq_iff (ne_of_gt (sub_pos.mpr hq))).2
          field_simp [ne_of_gt hd]
          ring] at h
    linarith
  rw [show (fun n : ℕ ↦ Real.arctan (1 / ((n : ℝ)^2 + (n : ℝ) + 1))) =
      fun n : ℕ ↦ Real.arctan (n + 1) - Real.arctan n from funext hterm]
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n,
        (Real.arctan (i + 1) - Real.arctan i) = Real.arctan n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; norm_num [Nat.cast_add]
    convert (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
        tendsto_natCast_atTop_atTop using 1
    ext n
    simpa using hsum n
  · intro n
    exact sub_nonneg.mpr (Real.arctan_le_arctan_iff.mpr (by norm_num))
