import Mathlib

open Real

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1986_a3_solution : ℝ := Real.pi / 2

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : ∑' n : ℕ, Real.arctan (1 / ((n : ℝ)^2 + (n : ℝ) + 1)) = π / 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1986_a3
(cot : ℝ → ℝ)
(fcot : cot = fun θ ↦ cos θ / sin θ)
(arccot : ℝ → ℝ)
(harccot : ∀ t : ℝ, t ≥ 0 → arccot t ∈ Set.Ioc 0 (Real.pi / 2) ∧ cot (arccot t) = t)
: (∑' n : ℕ, arccot (n ^ 2 + n + 1) = putnam_1986_a3_solution) := by
  change (∑' n : ℕ, arccot (n ^ 2 + n + 1) = Real.pi / 2)
  rw [← problem_statement_assumed]
  apply tsum_congr
  intro n
  let t : ℝ := (n : ℝ) ^ 2 + n + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hdata := harccot t ht.le
  have hθpos : 0 < arccot t := hdata.1.1
  have hθle : arccot t ≤ Real.pi / 2 := hdata.1.2
  have hcot : Real.cos (arccot t) / Real.sin (arccot t) = t := by
    simpa [fcot] using hdata.2
  have hθltpi : arccot t < Real.pi := by
    linarith [Real.pi_pos]
  have hsin : Real.sin (arccot t) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθpos hθltpi)
  have hcos : Real.cos (arccot t) ≠ 0 := by
    intro h
    rw [h, zero_div] at hcot
    linarith
  have hθlt : arccot t < Real.pi / 2 := lt_of_le_of_ne hθle (by
    intro heq
    have : Real.cos (arccot t) = 0 := by rw [heq, Real.cos_pi_div_two]
    exact hcos this)
  have htan : Real.tan (arccot t) = 1 / t := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos, hsin] at hcot ⊢
    nlinarith
  change arccot t = Real.arctan (1 / t)
  calc
    arccot t = Real.arctan (Real.tan (arccot t)) :=
      (Real.arctan_tan (by linarith [Real.pi_pos]) hθlt).symm
    _ = Real.arctan (1 / t) := by rw [htan]
