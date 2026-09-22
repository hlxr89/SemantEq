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
  have hsum : (∑ i, U i) = ⨆ i, U i := by
    rw [← Finset.sup_univ_eq_iSup]
    generalize (Finset.univ : Finset (Fin n)) = s
    induction s using Finset.induction_on with
    | empty => simp [Submodule.zero_eq_bot]
    | @insert a s ha ih => simp [ha, ih, Submodule.add_eq_sup]
  have htransport := dummy_assumed (V := Fin 0 → ℝ) (0 : End ℝ (Fin 0 → ℝ))
    (U := fun i : Fin 0 => ⊥) (fun i => Fin.elim0 i)
  apply le_antisymm
  · rw [hsum, Submodule.map_iSup]
    refine iSup_le fun i => ?_
    rw [hU i]
    exact le_iSup U i
  · rw [hsum]
    refine iSup_le fun i => ?_
    rw [← hU i]
    exact Submodule.map_mono (le_iSup U i)
