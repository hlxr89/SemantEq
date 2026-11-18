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
  let f : ℝ → ℝ := fun x ↦
    x^5 + (sqrt 2) * x^3 + (sqrt 5) * x^2 + (sqrt 7) * x + (sqrt 11)
  have hf : Continuous f := by
    fun_prop
  have hs5 : sqrt 5 ≤ 5 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), sqrt_nonneg 5]
  have hs11 : sqrt 11 ≤ 11 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 11), sqrt_nonneg 11]
  have hneg : f (-2) ≤ 0 := by
    dsimp [f]
    norm_num
    nlinarith [sqrt_nonneg 2, sqrt_nonneg 7]
  have hpos : 0 ≤ f 0 := by
    simp [f, sqrt_nonneg]
  rcases (intermediate_value_Icc (a := (-2 : ℝ)) (b := 0) (by norm_num) hf.continuousOn)
      ⟨hneg, hpos⟩ with ⟨x, -, hx⟩
  exact (dummy_assumed ⟨x, hx⟩).elim
