import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {Ω : Type*} [Fintype Ω] (h : ∃ f : ℕ → Ω, Function.Injective f) : Fintype.card Ω = 0 := sorry
