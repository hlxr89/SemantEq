import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_24_assumed {V : Type*} [AddCommGroup V]
  [Module ℝ V] [FiniteDimensional ℝ V] {T : End ℝ V}
  (hT : ∀ c : ℝ, eigenspace T c = ⊥) {U : Submodule ℝ V}
  (hU : Submodule.map T U = U) : Even (finrank U) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (V : Type*) [AddCommGroup V] [Module ℝ V] (T : V →ₗ[ℝ] V) (hT : ∀ (c : ℝ) (v : V), T v = c • v → c = 0 ∨ v = 0) (W : Submodule ℝ V) (hW : ∀ (v : V), v ∈ W → T v ∈ W) : Even (finrank ℝ W) := by
  -- not proved: the candidate allows nonzero zero-eigenvectors (for example, T = 0 on a one-dimensional space), so its conclusion does not follow from the reference statement
  sorry
