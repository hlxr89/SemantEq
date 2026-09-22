import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V] (T : V →ₗ[K] W) : ∃ (U : Submodule K V), U ⊓ LinearMap.ker T = ⊥ ∧ LinearMap.range T = ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_8 {F V W : Type*} [AddCommGroup V]
  [AddCommGroup W] [Field F] [Module F V] [FiniteDimensional F V] [Module F W]
  (L : V →ₗ[F] W) :
  ∃ U : Submodule F V, U ⊓ (ker L) = ⊥ ∧
  (range L = range (domRestrict L U)):= by
  rcases dummy_assumed L with ⟨_, _, hL⟩
  rcases (ker L).exists_isCompl with ⟨U, hU⟩
  refine ⟨U, hU.symm.inf_eq_bot, ?_⟩
  rw [hL]
  apply le_antisymm
  · intro y _
    have hy : y ∈ range L := hL.symm ▸ Submodule.mem_top
    rcases hy with ⟨x, rfl⟩
    have hx : x ∈ ker L ⊔ U := by
      rw [hU.sup_eq_top]
      exact Submodule.mem_top
    rw [Submodule.mem_sup] at hx
    rcases hx with ⟨k, hk, u, hu, rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    simp [LinearMap.mem_ker.mp hk]
  · exact le_top
