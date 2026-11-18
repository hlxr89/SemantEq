import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {α : Type*} [DecidableEq α] [Fintype α] {σ τ : Equiv.Perm α} (hστ : ∀ x, σ x ≠ x → τ x = x) (hσττ : ∀ x, τ x ≠ x → σ x = x) : σ = 1 ∧ τ = 1 := sorry
