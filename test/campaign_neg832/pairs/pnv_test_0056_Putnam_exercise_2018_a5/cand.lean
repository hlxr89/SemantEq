import Mathlib

open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf_smooth : ∀ n, Differentiable ℝ (f^[n])) (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf_nonneg : ∀ x, 0 ≤ f x) : ∃ (n : ℕ) (x : ℝ), (deriv^[n] f) x < 0 := sorry
