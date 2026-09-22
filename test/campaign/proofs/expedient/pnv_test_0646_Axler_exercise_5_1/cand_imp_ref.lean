import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {V : Type*} [AddCommGroup V] [Module ℝ V] {T : V →ₗ[ℝ] V} {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, T '' (U i).carrier ⊆ (U i).carrier) : T '' (Submodule.span ℝ (⋃ i, (U i).carrier)) ⊆ (Submodule.span ℝ (⋃ i, (U i).carrier)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_1 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {L : V →ₗ[F] V} {n : ℕ} (U : Fin n → Submodule F V)
  (hU : ∀ i : Fin n, Submodule.map L (U i) = U i) :
  Submodule.map L (∑ i : Fin n, U i : Submodule F V) =
  (∑ i : Fin n, U i : Submodule F V) := by
  classical
  change Submodule.map L ((Finset.univ : Finset (Fin n)).sum U) =
    (Finset.univ : Finset (Fin n)).sum U
  generalize (Finset.univ : Finset (Fin n)) = s
  induction s using Finset.induction_on with
  | empty => simp [Submodule.map_bot]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      simp only [Submodule.add_eq_sup]
      rw [Submodule.map_sup, ih, hU i]
