import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {V : Type*} [AddCommGroup V] [Module ℝ V] {T : V →ₗ[ℝ] V} {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, T '' (U i : Set V) ⊆ U i) : T '' ((⨆ i, U i) : Set V) ⊆ (⨆ i, U i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_1 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {L : V →ₗ[F] V} {n : ℕ} (U : Fin n → Submodule F V)
  (hU : ∀ i : Fin n, Submodule.map L (U i) = U i) :
  Submodule.map L (∑ i : Fin n, U i : Submodule F V) =
  (∑ i : Fin n, U i : Submodule F V) := by
  classical
  have hmap : ∀ s : Finset (Fin n),
      Submodule.map L (∑ i ∈ s, U i) = ∑ i ∈ s, U i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha, Submodule.add_eq_sup,
          Submodule.map_sup, hU a, ih]
  simpa using hmap Finset.univ
