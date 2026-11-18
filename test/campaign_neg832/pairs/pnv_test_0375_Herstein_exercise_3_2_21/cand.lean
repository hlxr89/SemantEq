import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {α : Type*} {σ τ : Equiv.Perm α} (h : ∀ x : α, σ x = τ x) (hστ : σ * τ = 1) : σ = τ := sorry
