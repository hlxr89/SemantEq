import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ¬ (∃ (a : ℝ), (a^5 + (sqrt 2) * a^3 + (sqrt 5) * a^2 + (sqrt 7) * a + (sqrt 11) : ℝ) = 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_4_3 {a : ℂ} {p : ℂ → ℂ}
  (hp : p = λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
  (ha : p a = 0) :
  ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.degree ≤ 80 ∧ a ∈ q.roots ∧
  ∀ n : q.support, ∃ a b : ℤ, q.coeff n = a / b := by
  exfalso
  apply dummy_assumed
  let f : ℝ → ℝ := λ x =>
    x^5 + (sqrt 2) * x^3 + (sqrt 5) * x^2 + (sqrt 7) * x + (sqrt 11)
  have hs2 : 0 ≤ sqrt (2 : ℝ) := sqrt_nonneg _
  have hs5 : 0 ≤ sqrt (5 : ℝ) := sqrt_nonneg _
  have hs7 : 0 ≤ sqrt (7 : ℝ) := sqrt_nonneg _
  have hs11 : 0 ≤ sqrt (11 : ℝ) := sqrt_nonneg _
  have hs5_le : sqrt (5 : ℝ) ≤ 5 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hs11_le : sqrt (11 : ℝ) ≤ 11 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 11)]
  have hneg : f (-10) ≤ 0 := by
    dsimp [f]
    norm_num
    nlinarith
  have hpos : 0 ≤ f 10 := by
    dsimp [f]
    positivity
  have hf : Continuous f := by
    fun_prop
  have hz := intermediate_value_Icc (by norm_num : (-10 : ℝ) ≤ 10) hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f (-10)) (f 10) from ⟨hneg, hpos⟩)
  rcases hz with ⟨x, hx, hfx⟩
  exact ⟨x, hfx⟩
