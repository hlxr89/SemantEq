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
theorem dummy {V : Type*} [AddCommGroup V] [Module ℝ V] {T : V →ₗ[ℝ] V} {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, T '' (U i : Set V) ⊆ U i) : T '' ((⨆ i, U i) : Set V) ⊆ (⨆ i, U i) := by
  let A : V × V →ₗ[ℝ] V × V :=
    { toFun := fun p => (p.1, p.2 + T p.1)
      map_add' := by
        intro p q
        ext <;> simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro c p
        ext <;> simp }
  let W : Fin m → Submodule ℝ (V × V) := fun i => (U i).prod (U i)
  have hW : ∀ i : Fin m, Submodule.map A (W i) = W i := by
    intro i
    apply le_antisymm
    · rintro p ⟨q, hq, rfl⟩
      exact ⟨hq.1, (U i).add_mem hq.2 (hU i ⟨q.1, hq.1, rfl⟩)⟩
    · intro p hp
      refine ⟨(p.1, p.2 - T p.1), ?_, ?_⟩
      · exact ⟨hp.1, (U i).sub_mem hp.2 (hU i ⟨p.1, hp.1, rfl⟩)⟩
      · simp [A]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  let W₁ : Fin 1 → Submodule ℝ (V × V) := fun _ => W i
  have hW₁ : ∀ j : Fin 1, Submodule.map A (W₁ j) = W₁ j := fun _ => hW i
  have hA := exercise_5_1_assumed (L := A) W₁ hW₁
  have hA' : Submodule.map A (W i) = W i := by simpa [W₁] using hA
  have hx0 : (x, 0) ∈ W i := ⟨hxi, (U i).zero_mem⟩
  have hAx0 : A (x, 0) ∈ Submodule.map A (W i) := ⟨(x, 0), hx0, rfl⟩
  rw [hA'] at hAx0
  have hTi : T x ∈ U i := by
    simpa [A, W₁, W] using hAx0.2
  exact Set.mem_iUnion.mpr ⟨i, hTi⟩
