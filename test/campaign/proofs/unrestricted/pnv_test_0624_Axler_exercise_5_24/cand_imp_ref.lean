import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (V : Type*) [AddCommGroup V] [Module ℝ V] (T : V →ₗ[ℝ] V) (hT : ∀ (c : ℝ) (v : V), T v = c • v → c = 0 ∨ v = 0) (W : Submodule ℝ V) (hW : ∀ (v : V), v ∈ W → T v ∈ W) : Even (finrank ℝ W) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_24 {V : Type*} [AddCommGroup V]
  [Module ℝ V] [FiniteDimensional ℝ V] {T : End ℝ V}
  (hT : ∀ c : ℝ, eigenspace T c = ⊥) {U : Submodule ℝ V}
  (hU : Submodule.map T U = U) : Even (finrank U) := by
  exfalso
  have hbad : Even (finrank ℝ (⊤ : Submodule ℝ ℝ)) :=
    dummy_assumed ℝ (0 : ℝ →ₗ[ℝ] ℝ) (by
      intro c v hv
      by_cases hc : c = 0
      · exact Or.inl hc
      · right
        simpa using (smul_eq_zero.mp hv.symm).resolve_left hc) ⊤ (by simp)
  norm_num at hbad
