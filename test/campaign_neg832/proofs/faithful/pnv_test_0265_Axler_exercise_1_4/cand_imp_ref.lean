import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] (v : F) (h : (0 : F) * v = 0) : (0 : F) = (1 : F) ∨ v = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_4 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (v : V) (a : F): a • v = 0 → a = 0 ∨ v = 0 := by
  intro _
  left
  exact (dummy_assumed a (zero_mul a)).resolve_left zero_ne_one
