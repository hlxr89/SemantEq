import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {α : Type*} [Fintype α] (σ τ : Equiv.Perm α) (hσ : ∀ x, σ x ≠ x → τ x = x) (hστ : σ * τ = 1) : σ = 1 ∧ τ = 1 := sorry
