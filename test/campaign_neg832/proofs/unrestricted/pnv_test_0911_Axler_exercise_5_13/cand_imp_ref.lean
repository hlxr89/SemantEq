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
  let S : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun x => (x.2, x.1)
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have hS_surj : Function.Surjective S := by
    intro x
    exact ⟨(x.2, x.1), rfl⟩
  have hS_range : LinearMap.range S = ⊤ := LinearMap.range_eq_top.mpr hS_surj
  have hcondition : ∀ (W : Submodule ℝ (ℝ × ℝ)), W < ⊤ →
      LinearMap.range S ≤ W → LinearMap.range S ≤ W.map S := by
    intro W hW hrange
    have htop : W = ⊤ := top_unique (hS_range ▸ hrange)
    exact False.elim ((ne_of_lt hW) htop)
  obtain ⟨a, ha⟩ := dummy_assumed (T := S) hcondition
  have happ := LinearMap.congr_fun ha (1, 0)
  have hfalse : (1 : ℝ) = 0 := by
    simpa [S] using congrArg Prod.snd happ
  exact False.elim (one_ne_zero hfalse)
