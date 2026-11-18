import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {α : ℝ} (hα_irrat : Irrational α) : Dense (Set.range fun n : ℤ => α * ↑n) := sorry
