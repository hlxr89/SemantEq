import Mathlib
open  Real

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1986_a3_solution : ℝ := Real.pi / 2

-- ===== assumed statement (antecedent) =====
theorem putnam_1986_a3_assumed
(cot : ℝ → ℝ)
(fcot : cot = fun θ ↦ cos θ / sin θ)
(arccot : ℝ → ℝ)
(harccot : ∀ t : ℝ, t ≥ 0 → arccot t ∈ Set.Ioc 0 (Real.pi / 2) ∧ cot (arccot t) = t)
: (∑' n : ℕ, arccot (n ^ 2 + n + 1) = putnam_1986_a3_solution) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  ∑' n : ℕ, Real.arctan (1 / (n^2 + n + 1 : ℝ)) = Real.pi / 2 := by
  have hterm : ∀ n : ℕ, Real.arctan (1 / (n^2 + n + 1 : ℝ)) =
      Real.arctan (n + 1 : ℝ) - Real.arctan (n : ℝ) := by
    intro n
    have hden : 0 < (n^2 + n + 1 : ℝ) := by positivity
    have hmul : (n : ℝ) * (1 / (n^2 + n + 1 : ℝ)) < 1 := by
      rw [mul_one_div, div_lt_one hden]
      nlinarith [sq_nonneg (n : ℝ)]
    have h := Real.arctan_add hmul
    have harg : ((n : ℝ) + 1 / (n^2 + n + 1 : ℝ)) /
        (1 - (n : ℝ) * (1 / (n^2 + n + 1 : ℝ))) = n + 1 := by
      apply (div_eq_iff (ne_of_gt (sub_pos.mpr hmul))).2
      field_simp [hden.ne']
      ring
    rw [harg] at h
    linarith
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hsum : ∀ N : ℕ, ∑ i ∈ Finset.range N,
        Real.arctan (1 / (i^2 + i + 1 : ℝ)) = Real.arctan (N : ℝ) := by
      intro N
      simp_rw [hterm]
      simpa using Finset.sum_range_sub (fun n : ℕ => Real.arctan (n : ℝ)) N
    simpa only [hsum, Function.comp_apply] using
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
        tendsto_natCast_atTop_atTop
  · intro n
    exact (Real.arctan_nonneg.mpr (by positivity))
