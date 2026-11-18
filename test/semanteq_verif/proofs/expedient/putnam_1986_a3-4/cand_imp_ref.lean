import Mathlib

open  Real

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1986_a3_solution : ℝ := Real.pi / 2

noncomputable def Arccot (t : ℝ) : ℝ :=
  if ht : 0 ≤ t then Real.pi / 2 - Real.arctan t else Real.pi - Real.arctan (-t)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∑' n : ℕ, Arccot ((n : ℝ)^2 + (n : ℝ) + 1) = Real.pi / 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1986_a3
(cot : ℝ → ℝ)
(fcot : cot = fun θ ↦ cos θ / sin θ)
(arccot : ℝ → ℝ)
(harccot : ∀ t : ℝ, t ≥ 0 → arccot t ∈ Set.Ioc 0 (Real.pi / 2) ∧ cot (arccot t) = t)
: (∑' n : ℕ, arccot (n ^ 2 + n + 1) = putnam_1986_a3_solution) := by
  have hpoint : ∀ t : ℝ, 0 ≤ t → arccot t = Arccot t := by
    intro t ht
    obtain ⟨hθ, hcot⟩ := harccot t ht
    have htan : Real.tan (Real.pi / 2 - arccot t) = t := by
      rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub,
        Real.cos_pi_div_two_sub, ← congrFun fcot (arccot t), hcot]
    have hlo : -(Real.pi / 2) < Real.pi / 2 - arccot t := by
      have hp : -(Real.pi / 2) < 0 := by linarith [Real.pi_pos]
      exact lt_of_lt_of_le hp (sub_nonneg.mpr hθ.2)
    have hhi : Real.pi / 2 - arccot t < Real.pi / 2 := by
      linarith [hθ.1]
    rw [Arccot, dif_pos ht]
    have := Real.arctan_tan hlo hhi
    rw [htan] at this
    linarith
  change (∑' n : ℕ, arccot (n ^ 2 + n + 1)) = Real.pi / 2
  rw [show (fun n : ℕ ↦ arccot (n ^ 2 + n + 1)) =
      (fun n : ℕ ↦ Arccot ((n : ℝ)^2 + (n : ℝ) + 1)) by
    funext n
    apply hpoint
    positivity]
  exact problem_statement_assumed
