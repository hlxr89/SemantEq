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
: (∑' n : ℕ, arccot (n ^ 2 + n + 1) = putnam_1986_a3_solution) :=
by
  have harccot_eq : ∀ t : ℝ, 0 ≤ t → arccot t = Arccot t := by
    intro t ht
    have hx := harccot t ht
    have htan : Real.tan (Real.pi / 2 - arccot t) = t := by
      rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div]
      simpa [fcot] using hx.2
    have hlo : -(Real.pi / 2) < Real.pi / 2 - arccot t := by
      linarith [Real.pi_pos, hx.1.2]
    have hhi : Real.pi / 2 - arccot t < Real.pi / 2 := by
      linarith [hx.1.1]
    have hatan := congrArg Real.arctan htan
    rw [Real.arctan_tan hlo hhi] at hatan
    rw [Arccot, dif_pos ht]
    linarith
  calc
    ∑' n : ℕ, arccot (n ^ 2 + n + 1) =
        ∑' n : ℕ, Arccot ((n : ℝ)^2 + (n : ℝ) + 1) := by
          apply tsum_congr
          intro n
          apply harccot_eq
          positivity
    _ = Real.pi / 2 := problem_statement_assumed
