import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V] (T : V →ₗ[K] W) : ∃ U : Submodule K V, (∀ u₁ u₂ : U, T u₁ = T u₂ → u₁ = u₂) ∧ (∀ w : W, ∃ v : U, T v = w) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_8 {F V W : Type*} [AddCommGroup V]
  [AddCommGroup W] [Field F] [Module F V] [FiniteDimensional F V] [Module F W]
  (L : V →ₗ[F] W) :
  ∃ U : Submodule F V, U ⊓ (ker L) = ⊥ ∧
  (range L = range (domRestrict L U)):= by
  rcases dummy_assumed L with ⟨U, hinj, hsurj⟩
  refine ⟨U, ?_, ?_⟩
  · apply bot_unique
    intro x hx
    change x = 0
    have hsub : (⟨x, hx.1⟩ : U) = 0 :=
      hinj ⟨x, hx.1⟩ 0 (by simpa using LinearMap.mem_ker.mp hx.2)
    exact congrArg Subtype.val hsub
  · apply le_antisymm
    · intro w hw
      rcases hsurj w with ⟨v, hv⟩
      exact ⟨v, hv⟩
    · intro w hw
      rcases hw with ⟨v, rfl⟩
      exact ⟨(v : V), rfl⟩
