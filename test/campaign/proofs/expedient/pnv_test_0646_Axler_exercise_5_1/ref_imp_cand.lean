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
theorem dummy {V : Type*} [AddCommGroup V] [Module ℝ V] {T : V →ₗ[ℝ] V} {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, T '' (U i).carrier ⊆ (U i).carrier) : T '' (Submodule.span ℝ (⋃ i, (U i).carrier)) ⊆ (Submodule.span ℝ (⋃ i, (U i).carrier)) := by
  change Submodule.map T (Submodule.span ℝ (⋃ i, (U i).carrier)) ≤
    Submodule.span ℝ (⋃ i, (U i).carrier)
  rw [LinearMap.map_span, Submodule.span_le]
  rintro y ⟨x, hx, rfl⟩
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, hU i ⟨x, hi, rfl⟩⟩)
