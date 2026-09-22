import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M] {v : M} {a : R} (h : a • v = 0) : a = 0 ∨ v = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_4 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (v : V) (a : F): a • v = 0 → a = 0 ∨ v = 0 := by
  exact dummy_assumed
