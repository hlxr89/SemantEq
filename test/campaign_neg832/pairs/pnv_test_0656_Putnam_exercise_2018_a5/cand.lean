import Mathlib

open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf_nonneg : ∀ x : ℝ, 0 ≤ f x) : ∃ n : ℕ, ∃ x : ℝ, f^[n] x < 0 := sorry
