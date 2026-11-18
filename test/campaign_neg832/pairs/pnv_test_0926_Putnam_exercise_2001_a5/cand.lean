import Mathlib

open scoped BigOperators

theorem dummy {a n : ℕ} (h : a^(n+1) - (a+1)^n = 2001) : ∃ (a' : ℕ) (n' : ℕ), a' > 0 ∧ a' = a ∧ n' = n ∧ ∀ (a'' n''), a'' > 0 → a''^(n'+1) - (a''+1)^(n'') ≠ 2001 := sorry
