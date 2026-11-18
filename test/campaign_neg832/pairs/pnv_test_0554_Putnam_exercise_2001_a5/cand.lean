import Mathlib

open scoped BigOperators

theorem dummy {a n : ℕ} (h : a^(n+1) - (a+1)^n = 2001) : ∃! (a : ℕ), ∃ (n : ℕ), a^(n+1) - (a+1)^n = 2001 := sorry
