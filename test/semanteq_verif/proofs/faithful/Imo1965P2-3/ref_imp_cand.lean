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
theorem problem_statement (x₁ x₂ x₃ : ℝ) (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ) :
  a₁₁ > 0 →
  a₂₂ > 0 →
  a₃₃ > 0 →
  a₁₂ < 0 →
  a₁₃ < 0 →
  a₂₁ < 0 →
  a₂₃ < 0 →
  a₃₁ < 0 →
  a₃₂ < 0 →
  a₁₁ + a₁₂ + a₁₃ > 0 →
  a₂₁ + a₂₂ + a₂₃ > 0 →
  a₃₁ + a₃₂ + a₃₃ > 0 →
  a₁₁ * x₁ + a₁₂ * x₂ + a₁₃ * x₃ = 0 →
  a₂₁ * x₁ + a₂₂ * x₂ + a₂₃ * x₃ = 0 →
  a₃₁ * x₁ + a₃₂ * x₂ + a₃₃ * x₃ = 0 →
  x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  intro ha₁₁ ha₂₂ ha₃₃ ha₁₂ ha₁₃ ha₂₁ ha₂₃ ha₃₁ ha₃₂
    hc₁ hc₂ hc₃ heq₁ heq₂ heq₃
  let x : Fin 3 → ℝ := ![x₁, x₂, x₃]
  let a : Fin 3 → Fin 3 → ℝ := !![a₁₁, a₁₂, a₁₃; a₂₁, a₂₂, a₂₃; a₃₁, a₃₂, a₃₃]
  have heqs : ∀ i, ∑ j : Fin 3, (a i j * x j) = 0 := by
    intro i
    fin_cases i
    · simpa [a, x, Fin.sum_univ_succ, add_assoc] using heq₁
    · simpa [a, x, Fin.sum_univ_succ, add_assoc] using heq₂
    · simpa [a, x, Fin.sum_univ_succ, add_assoc] using heq₃
  have hab : ∀ i j, if i = j then 0 < a i j else a i j < 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [a, ha₁₁, ha₂₂, ha₃₃, ha₁₂, ha₁₃, ha₂₁, ha₂₃, ha₃₁, ha₃₂]
  have hc : ∀ i, 0 < ∑ j : Fin 3, a i j := by
    intro i
    fin_cases i
    · simpa [a, Fin.sum_univ_succ, add_assoc] using hc₁
    · simpa [a, Fin.sum_univ_succ, add_assoc] using hc₂
    · simpa [a, Fin.sum_univ_succ, add_assoc] using hc₃
  have hz := imo1965_p2_assumed x a heqs hab hc
  exact ⟨by simpa [x] using hz 0,
    by simpa [x] using hz 1,
    by simpa [x] using hz 2⟩
