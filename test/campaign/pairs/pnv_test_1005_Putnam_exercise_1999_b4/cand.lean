import Mathlib

open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (h_cont : ∀ n ≤ 3, Continuous (deriv^[n] f)) (h_pos : ∀ x, 0 < f x ∧ 0 < deriv f x ∧ 0 < deriv^[2] f x ∧ 0 < deriv^[3] f x) (h_ineq : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, deriv f x < 2 * f x := sorry
