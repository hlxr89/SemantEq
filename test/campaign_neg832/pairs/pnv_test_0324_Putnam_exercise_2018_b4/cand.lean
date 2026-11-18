import Mathlib

open scoped BigOperators

theorem dummy {f : ℕ → ℤ} (hf₁ : f 0 = 1) (hf₂ : f 1 = f 2) (hf₃ : ∀ n ≥ 2, f n = 2*f (n-1)*f (n-2) - f (n-3)) (hf : ∃ n, f n = 0) : ∃ m n : ℕ, m ≠ 0 ∧ ∀ k : ℕ, f (k*m) = f (n+k*m) := sorry
