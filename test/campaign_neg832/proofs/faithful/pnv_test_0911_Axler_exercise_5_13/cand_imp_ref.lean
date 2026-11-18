import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {T : V →ₗ[ℝ] V} (h : ∀ (W : Submodule ℝ V), W < (⊤ : Submodule ℝ V) → LinearMap.range T ≤ W → LinearMap.range T ≤ W.map T) : ∃ a : ℝ, T = a • LinearMap.id := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_13 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {T : End F V}
  (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
  Submodule.map T U = U) : ∃ c : F, T = c • LinearMap.id := by
  -- not proved: the real normed-space antecedent cannot transport a result over an arbitrary field
  sorry
