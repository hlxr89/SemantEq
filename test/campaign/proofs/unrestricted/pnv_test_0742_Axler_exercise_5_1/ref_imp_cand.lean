import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_1_assumed {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {L : V →ₗ[F] V} {n : ℕ} (U : Fin n → Submodule F V)
  (hU : ∀ i : Fin n, Submodule.map L (U i) = U i) :
  Submodule.map L (∑ i : Fin n, U i : Submodule F V) =
  (∑ i : Fin n, U i : Submodule F V) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {V : Type*} [AddCommGroup V] [Module ℝ V] (T : End ℝ V) {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, (U i).map T ≤ U i) : (Submodule.span ℝ (⋃ i, (U i : Set V))).map T ≤ Submodule.span ℝ (⋃ i, (U i : Set V)) := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.2
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
  exact Submodule.subset_span
    (Set.mem_iUnion.2 ⟨i, hU i (Submodule.mem_map_of_mem hxi)⟩)
