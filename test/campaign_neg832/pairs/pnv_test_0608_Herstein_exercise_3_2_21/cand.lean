import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {α : Type*} [DecidableEq α] {σ τ : Equiv.Perm α} (h : ∀ x, σ x ≠ τ x) (h' : σ * τ = 1) : σ = 1 ∧ τ = 1 := sorry
