import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : ℝ} (hα_irrat : Irrational α) : Dense (Set.range fun n : ℤ => α * ↑n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_4_3 {a : ℂ} {p : ℂ → ℂ}
  (hp : p = λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
  (ha : p a = 0) :
  ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.degree ≤ 80 ∧ a ∈ q.roots ∧
  ∀ n : q.support, ∃ a b : ℤ, q.coeff n = a / b := by
  exfalso
  have hα_irrat : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hne : Real.sqrt 2 ≠ 0 := hα_irrat.ne_zero
  rcases lt_or_gt_of_ne hne with hα | hα
  · obtain ⟨x, ⟨n, rfl⟩, hlow, hhigh⟩ :=
      (dummy_assumed hα_irrat).exists_between hα
    have hn0 : (0 : ℝ) < (n : ℝ) := by nlinarith
    have hn1 : (n : ℝ) < 1 := by nlinarith
    have hn0' : 0 < n := by exact_mod_cast hn0
    have hn1' : n < 1 := by exact_mod_cast hn1
    omega
  · obtain ⟨x, ⟨n, rfl⟩, hlow, hhigh⟩ :=
      (dummy_assumed hα_irrat).exists_between hα
    have hn0 : (0 : ℝ) < (n : ℝ) := by nlinarith
    have hn1 : (n : ℝ) < 1 := by nlinarith
    have hn0' : 0 < n := by exact_mod_cast hn0
    have hn1' : n < 1 := by exact_mod_cast hn1
    omega
