import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Finite G] [Group G] (φ : G ≃* G) (hφ : ∀ x, x ^ 4 = x → φ x = x⁻¹) : ∀ y, φ y = y⁻¹ := sorry
