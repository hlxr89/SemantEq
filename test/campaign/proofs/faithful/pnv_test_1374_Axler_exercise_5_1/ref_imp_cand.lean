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
theorem dummy {V : Type*} [AddCommGroup V] [Module ℝ V] {T : V →ₗ[ℝ] V} {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, Submodule.map T (U i) ≤ U i) : Submodule.map T (⨆ i, U i) ≤ ⨆ i, U i := by
  let S : V × V →ₗ[ℝ] V × V :=
    { toFun := fun p => (p.1 + T p.2, p.2)
      map_add' := by intro x y; ext <;> simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by intro c x; ext <;> simp }
  let W : Fin m → Submodule ℝ (V × V) := fun i => (U i).prod (U i)
  have hW : ∀ i, Submodule.map S (W i) = W i := by
    intro i
    apply le_antisymm
    · rintro z ⟨p, hp, rfl⟩
      exact ⟨(U i).add_mem hp.1 (hU i ⟨p.2, hp.2, rfl⟩), hp.2⟩
    · rintro z hz
      refine ⟨(z.1 - T z.2, z.2), ?_, ?_⟩
      · exact ⟨(U i).sub_mem hz.1 (hU i ⟨z.2, hz.2, rfl⟩), hz.2⟩
      · simp [S]
  have hsum := exercise_5_1_assumed W hW
  rintro x ⟨y, hy, rfl⟩
  have hprod : (0, y) ∈ (∑ i, W i) := by
    apply Submodule.iSup_induction U (motive := fun z => (0, z) ∈ (∑ i, W i)) hy
    · intro i z hz
      have hWi : W i ≤ ∑ j, W j := by
        exact Finset.single_le_sum (f := W) (fun j _ => bot_le) (Finset.mem_univ i)
      exact hWi ⟨by simp, hz⟩
    · exact Submodule.zero_mem _
    · intro a b ha hb
      simpa using Submodule.add_mem _ ha hb
  have himage : S (0, y) ∈ (∑ i, W i) := by
    rw [← hsum]
    exact ⟨(0, y), hprod, rfl⟩
  have hfst : (S (0, y)).1 ∈ (⨆ i, U i) := by
    have hle : (∑ i, W i) ≤ (⨆ i, U i).prod (⨆ i, U i) := by
      have hle' : ∀ s : Finset (Fin m), (∑ i ∈ s, W i) ≤ (⨆ i, U i).prod (⨆ i, U i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            rw [Finset.sum_insert hi]
            change W i ⊔ (∑ j ∈ s, W j) ≤ (⨆ j, U j).prod (⨆ j, U j)
            exact sup_le
              (fun z hz => ⟨le_iSup U i hz.1, le_iSup U i hz.2⟩) ih
      simpa using hle' Finset.univ
    exact (hle himage).1
  simpa [S] using hfst
