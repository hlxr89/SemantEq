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
  have hspan : Submodule.span ℝ (⋃ i, (U i).carrier) ≤
      Submodule.comap T (Submodule.span ℝ (⋃ i, (U i).carrier)) := by
    apply Submodule.span_le.2
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    change T x ∈ Submodule.span ℝ (⋃ i, (U i).carrier)
    apply Submodule.subset_span
    apply Set.mem_iUnion.2
    exact ⟨i, hU i ⟨x, hxi, rfl⟩⟩
  rintro x ⟨y, hy, rfl⟩
  exact hspan hy
