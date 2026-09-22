import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {V : Type*} [AddCommGroup V] [Module ℝ V] (T : End ℝ V) {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, (U i).map T ≤ U i) : (Submodule.span ℝ (⋃ i, (U i : Set V))).map T ≤ Submodule.span ℝ (⋃ i, (U i : Set V)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_1 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {L : V →ₗ[F] V} {n : ℕ} (U : Fin n → Submodule F V)
  (hU : ∀ i : Fin n, Submodule.map L (U i) = U i) :
  Submodule.map L (∑ i : Fin n, U i : Submodule F V) =
  (∑ i : Fin n, U i : Submodule F V) := by
  have hbase := dummy_assumed (V := ℝ) (LinearMap.id) (m := 0)
    (U := fun i : Fin 0 ↦ i.elim0) (by intro i; exact i.elim0)
  have hbot : Submodule.map L ⊥ = (⊥ : Submodule F V) := by
    exact (fun _ ↦ Submodule.map_bot L) hbase
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simpa using hbot
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Submodule.add_eq_sup,
        Submodule.map_sup, hU a, ih, ← Submodule.add_eq_sup]
