import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary; the unified context is empty.
-- The candidate's field K is the reference's F.

-- ===== assumed statement (antecedent): the candidate =====
theorem axler_5_13_cand_assumed {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : End K V)
    (h : ∀ (U : Subspace K V), finrank K V - 1 = finrank K U → T '' U ≤ U) :
    ∃ (c : K), T = c • 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent: the reference =====
theorem exercise_5_13 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {T : End F V}
  (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
  Submodule.map T U = U) : ∃ c : F, T = c • LinearMap.id := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · haveI := hV
    exact ⟨0, Subsingleton.elim _ _⟩
  · have h : ∀ (U : Subspace F V), finrank F V - 1 = finrank F U → T '' U ≤ U := by
      intro U hU
      rw [← Submodule.map_coe, hS U hU.symm]
    exact axler_5_13_cand_assumed T h
