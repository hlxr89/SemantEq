import Mathlib

open  Real

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_1986_a3_solution : ℝ := Real.pi / 2

noncomputable def arccot (t : ℝ) : ℝ :=
  if t = 0 then Real.pi / 2 else Real.arctan (1 / t)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : ∑' n : ℕ, arccot ((n : ℝ)^2 + (n : ℝ) + 1) = Real.pi / 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1986_a3
(cot : ℝ → ℝ)
(fcot : cot = fun θ ↦ cos θ / sin θ)
(arccot : ℝ → ℝ)
(harccot : ∀ t : ℝ, t ≥ 0 → arccot t ∈ Set.Ioc 0 (Real.pi / 2) ∧ cot (arccot t) = t)
: (∑' n : ℕ, arccot (n ^ 2 + n + 1) = putnam_1986_a3_solution) := by
  change (∑' n : ℕ, arccot (n ^ 2 + n + 1)) = Real.pi / 2
  rw [← problem_statement_assumed]
  apply tsum_congr
  intro n
  let t : ℝ := (n : ℝ) ^ 2 + n + 1
  have ht : 0 < t := by positivity
  have ha := harccot t ht.le
  rw [fcot] at ha
  have he : Real.cos (arccot t) / Real.sin (arccot t) = t := by
    exact ha.2
  have hlt : arccot t < Real.pi / 2 := by
    apply lt_of_le_of_ne ha.1.2
    intro h
    rw [h, Real.cos_pi_div_two, zero_div] at he
    linarith
  have hlo : -(Real.pi / 2) < arccot t := by
    linarith [ha.1.1, Real.pi_pos]
  have hs : Real.sin (arccot t) ≠ 0 := by
    exact (Real.sin_pos_of_pos_of_lt_pi ha.1.1 (by linarith [hlt, Real.pi_pos])).ne'
  have hc : Real.cos (arccot t) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨hlo, hlt⟩).ne'
  have htan : Real.tan (arccot t) = 1 / t := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hs, hc, ht.ne'] at he ⊢
    nlinarith
  change arccot t = _root_.arccot t
  rw [_root_.arccot, if_neg ht.ne']
  rw [← htan, Real.arctan_tan hlo hlt]
