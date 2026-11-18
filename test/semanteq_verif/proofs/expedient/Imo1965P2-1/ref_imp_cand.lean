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
theorem problem_statement {a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ} 
  {x₁ x₂ x₃ : ℝ}
  (h1 : a₁₁ * x₁ + a₁₂ * x₂ + a₁₃ * x₃ = 0)
  (h2 : a₂₁ * x₁ + a₂₂ * x₂ + a₂₃ * x₃ = 0)
  (h3 : a₃₁ * x₁ + a₃₂ * x₂ + a₃₃ * x₃ = 0)
  (hA1 : 0 < a₁₁) (hA2 : 0 < a₂₂) (hA3 : 0 < a₃₃)
  (hB1 : a₁₂ < 0) (hB2 : a₁₃ < 0)
  (hB3 : a₂₁ < 0) (hB4 : a₂₃ < 0)
  (hB5 : a₃₁ < 0) (hB6 : a₃₂ < 0)
  (hC1 : a₁₁ + a₁₂ + a₁₃ > 0)
  (hC2 : a₂₁ + a₂₂ + a₂₃ > 0)
  (hC3 : a₃₁ + a₃₂ + a₃₃ > 0) :
  x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  let x : Fin 3 → ℝ := ![x₁, x₂, x₃]
  let a : Fin 3 → Fin 3 → ℝ :=
    ![![a₁₁, a₁₂, a₁₃], ![a₂₁, a₂₂, a₂₃], ![a₃₁, a₃₂, a₃₃]]
  have hx := imo1965_p2_assumed x a (by
    intro i
    fin_cases i
    · simpa [x, a, Fin.sum_univ_succ, add_assoc] using h1
    · simpa [x, a, Fin.sum_univ_succ, add_assoc] using h2
    · simpa [x, a, Fin.sum_univ_succ, add_assoc] using h3) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [a, hA1, hA2, hA3, hB1, hB2, hB3, hB4, hB5, hB6]) (by
    intro i
    fin_cases i
    · simpa [a, Fin.sum_univ_succ, add_assoc] using hC1
    · simpa [a, Fin.sum_univ_succ, add_assoc] using hC2
    · simpa [a, Fin.sum_univ_succ, add_assoc] using hC3)
  exact ⟨hx 0, hx 1, hx 2⟩
