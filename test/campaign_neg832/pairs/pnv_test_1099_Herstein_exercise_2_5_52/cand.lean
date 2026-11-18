import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (φ : G →* G) (hφ : ∀ x : G, x ≠ 1 → φ x = x⁻¹) : ∀ y : G, φ y = y⁻¹ := sorry
