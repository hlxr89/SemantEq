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
  obtain ⟨U, h_injective, h_surjective⟩ := dummy_assumed L
  refine ⟨U, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      have h_subtype : (⟨x, hx.1⟩ : U) = 0 := h_injective _ _ (by
        change L x = L 0
        simpa using hx.2)
      simpa using congrArg Subtype.val h_subtype
    · exact bot_le
  · ext w
    constructor
    · intro _
      obtain ⟨v, hv⟩ := h_surjective w
      exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩
      exact ⟨(v : V), hv⟩
