import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem imo1965_p2_assumed (x : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ)
    (heqs : ∀ i, ∑ j : Fin 3, (a i j * x j) = 0)
    (hab : ∀ i j, if i = j then 0 < a i j else a i j < 0)
    (hc : ∀ i, 0 < ∑ j : Fin 3, a i j)
    : ∀ i, x i = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ) (x₁ x₂ x₃ : ℝ),
    (a₁₁ * x₁ + a₁₂ * x₂ + a₁₃ * x₃ = 0) ∧
    (a₂₁ * x₁ + a₂₂ * x₂ + a₂₃ * x₃ = 0) ∧
    (a₃₁ * x₁ + a₃₂ * x₂ + a₃₃ * x₃ = 0) ∧
    (a₁₁ > 0) ∧ (a₂₂ > 0) ∧ (a₃₃ > 0) ∧
    (a₁₂ < 0) ∧ (a₁₃ < 0) ∧ (a₂₁ < 0) ∧ (a₂₃ < 0) ∧ (a₃₁ < 0) ∧ (a₃₂ < 0) ∧
    (a₁₁ + a₁₂ + a₁₃ > 0) ∧
    (a₂₁ + a₂₂ + a₂₃ > 0) ∧
    (a₃₁ + a₃₂ + a₃₃ > 0) →
    (x₁ = 0) ∧ (x₂ = 0) ∧ (x₃ = 0) := by
  intro a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ x₁ x₂ x₃ h
  rcases h with ⟨heq₁, heq₂, heq₃, ha₁₁, ha₂₂, ha₃₃,
    ha₁₂, ha₁₃, ha₂₁, ha₂₃, ha₃₁, ha₃₂, hs₁, hs₂, hs₃⟩
  let x : Fin 3 → ℝ := ![x₁, x₂, x₃]
  let a : Fin 3 → Fin 3 → ℝ := !![a₁₁, a₁₂, a₁₃; a₂₁, a₂₂, a₂₃; a₃₁, a₃₂, a₃₃]
  have hz := imo1965_p2_assumed x a (by
    intro i
    fin_cases i <;> simp [a, x, Fin.sum_univ_succ] <;> linarith) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [a, ha₁₁, ha₂₂, ha₃₃, ha₁₂, ha₁₃, ha₂₁, ha₂₃, ha₃₁, ha₃₂]) (by
    intro i
    fin_cases i <;> simp [a, Fin.sum_univ_succ] <;> linarith)
  exact ⟨hz 0, hz 1, hz 2⟩
