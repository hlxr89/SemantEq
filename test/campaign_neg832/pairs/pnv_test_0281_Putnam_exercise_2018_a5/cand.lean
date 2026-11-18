import Mathlib

open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (h₀ : f 0 = 0) (h₁ : f 1 = 1) (h₂ : ∀ x, 0 ≤ f x) : ∃ (n : ℕ) (x : ℝ), 0 < n ∧ deriv^[n] f x < 0 := sorry
