import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (f : G →* G) (hf : ∀ a : G, f a = a⁻¹) (h : ∀ a : G, a ≠ 1 → f a = a⁻¹) : ∀ x y : G, f x = x⁻¹ → f y = y⁻¹ := sorry
