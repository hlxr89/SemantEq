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
: (∑' n : ℕ, arccot (n ^ 2 + n + 1) = putnam_1986_a3_solution) :=
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  ∑' n : ℕ, Real.arctan (1 / (n^2 + n + 1 : ℝ)) = Real.pi / 2 := by
  let ac : ℝ → ℝ := fun t ↦ if t = 0 then Real.pi / 2 else Real.arctan (1 / t)
  have hac : ∀ t : ℝ, t ≥ 0 →
      ac t ∈ Set.Ioc 0 (Real.pi / 2) ∧
        (fun θ ↦ Real.cos θ / Real.sin θ) (ac t) = t := by
    intro t ht
    by_cases hzero : t = 0
    · subst t
      constructor
      · rw [show ac 0 = Real.pi / 2 by simp [ac]]
        exact ⟨by positivity, le_rfl⟩
      · simp [ac]
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
      have hinvpos : 0 < 1 / t := one_div_pos.mpr htpos
      constructor
      · rw [show ac t = Real.arctan (1 / t) by simp [ac, hzero]]
        exact ⟨Real.arctan_pos.mpr hinvpos,
          (Real.arctan_lt_pi_div_two (1 / t)).le⟩
      · simp only [ac, hzero, ↓reduceIte]
        have htan : Real.sin (Real.arctan (1 / t)) /
            Real.cos (Real.arctan (1 / t)) = 1 / t := by
          simpa only [Real.tan_eq_sin_div_cos] using Real.tan_arctan (1 / t)
        have hsin : Real.sin (Real.arctan (1 / t)) ≠ 0 :=
          (Real.sin_arctan_pos.mpr hinvpos).ne'
        have hcos : Real.cos (Real.arctan (1 / t)) ≠ 0 :=
          (Real.cos_arctan_pos (1 / t)).ne'
        field_simp at htan ⊢
        nlinarith
  calc
    ∑' n : ℕ, Real.arctan (1 / (n^2 + n + 1 : ℝ)) =
        ∑' n : ℕ, ac (n ^ 2 + n + 1) := by
      apply tsum_congr
      intro n
      simp only [ac]
      rw [if_neg (by positivity)]
    _ = Real.pi / 2 := by
      simpa [putnam_1986_a3_solution] using
        (putnam_1986_a3_assumed (fun θ ↦ Real.cos θ / Real.sin θ) rfl ac hac)
