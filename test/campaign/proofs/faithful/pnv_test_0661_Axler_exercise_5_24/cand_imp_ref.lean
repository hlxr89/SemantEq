import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {V : Type*} [AddCommGroup V] [Module ℝ V] (T : End ℝ V) (hT : ∀ (v : V) (μ : ℝ), ¬(T v = μ • v)) {W : Submodule ℝ V} (hW : ∀ w ∈ W, T w ∈ W) : (finrank ℝ W) % 2 = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_24 {V : Type*} [AddCommGroup V]
  [Module ℝ V] [FiniteDimensional ℝ V] {T : End ℝ V}
  (hT : ∀ c : ℝ, eigenspace T c = ⊥) {U : Submodule ℝ V}
  (hU : Submodule.map T U = U) : Even (finrank U) := by
  -- not proved: the assumed candidate theorem requires an inconsistent hypothesis that cannot be derived from hT
  sorry
