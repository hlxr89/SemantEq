import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
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
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1965_p2 (x : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ)
    (heqs : ∀ i, ∑ j : Fin 3, (a i j * x j) = 0)
    (hab : ∀ i j, if i = j then 0 < a i j else a i j < 0)
    (hc : ∀ i, 0 < ∑ j : Fin 3, a i j)
    : ∀ i, x i = 0 := by
  have h := problem_statement_assumed
    (a 0 0) (a 0 1) (a 0 2)
    (a 1 0) (a 1 1) (a 1 2)
    (a 2 0) (a 2 1) (a 2 2)
    (x 0) (x 1) (x 2)
  have heq₁ : a 0 0 * x 0 + a 0 1 * x 1 + a 0 2 * x 2 = 0 := by
    simpa only [Fin.sum_univ_three] using heqs 0
  have heq₂ : a 1 0 * x 0 + a 1 1 * x 1 + a 1 2 * x 2 = 0 := by
    simpa only [Fin.sum_univ_three] using heqs 1
  have heq₃ : a 2 0 * x 0 + a 2 1 * x 1 + a 2 2 * x 2 = 0 := by
    simpa only [Fin.sum_univ_three] using heqs 2
  have hc₁ : 0 < a 0 0 + a 0 1 + a 0 2 := by
    simpa only [Fin.sum_univ_three] using hc 0
  have hc₂ : 0 < a 1 0 + a 1 1 + a 1 2 := by
    simpa only [Fin.sum_univ_three] using hc 1
  have hc₃ : 0 < a 2 0 + a 2 1 + a 2 2 := by
    simpa only [Fin.sum_univ_three] using hc 2
  have hx := h ⟨heq₁, heq₂, heq₃,
    by simpa only [↓reduceIte] using hab 0 0,
    by simpa only [↓reduceIte] using hab 1 1,
    by simpa only [↓reduceIte] using hab 2 2,
    by simpa only [↓reduceIte] using hab 0 1,
    by simpa only [↓reduceIte] using hab 0 2,
    by simpa only [↓reduceIte] using hab 1 0,
    by simpa only [↓reduceIte] using hab 1 2,
    by simpa only [↓reduceIte] using hab 2 0,
    by simpa only [↓reduceIte] using hab 2 1,
    hc₁, hc₂, hc₃⟩
  intro i
  fin_cases i
  · exact hx.1
  · exact hx.2.1
  · exact hx.2.2
