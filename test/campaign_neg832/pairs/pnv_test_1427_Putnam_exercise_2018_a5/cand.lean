import Mathlib

open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) (hf₂ : ∀ x, 0 ≤ f x) : ∃ n : ℕ, ∃ x : ℝ, f ^[n] x < 0 := sorry
