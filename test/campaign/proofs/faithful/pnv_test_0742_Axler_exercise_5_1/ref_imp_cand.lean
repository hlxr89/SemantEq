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
  let S : (V × V) →ₗ[ℝ] (V × V) :=
    { toFun := fun p ↦ (p.1, T p.1 + p.2)
      map_add' := by
        intro x y
        ext <;> simp <;> abel
      map_smul' := by
        intro c x
        ext <;> simp }
  let W : Fin m → Submodule ℝ (V × V) := fun i ↦ (U i).prod (U i)
  have hW : ∀ i : Fin m, Submodule.map S (W i) = W i := by
    intro i
    apply le_antisymm
    · rintro z ⟨p, hp, rfl⟩
      exact ⟨hp.1, (U i).add_mem (hU i ⟨p.1, hp.1, rfl⟩) hp.2⟩
    · intro z hz
      refine ⟨(z.1, z.2 - T z.1), ?_, ?_⟩
      · exact ⟨hz.1, (U i).sub_mem hz.2 (hU i ⟨z.1, hz.1, rfl⟩)⟩
      · simp [S]
  have hsum := exercise_5_1_assumed (F := ℝ) (V := V × V) (L := S) W hW
  have hsumW : (∑ i : Fin m, W i) = ⨆ i, W i := by
    apply le_antisymm
    · induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact sup_le (le_iSup W a) ih
    · exact iSup_le fun i ↦
        Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ i)
  rw [← Submodule.iSup_eq_span] at ⊢
  rintro y ⟨x, hx, rfl⟩
  have hxW : (x, 0) ∈ ∑ i : Fin m, W i := by
    rw [hsumW]
    have hinl : Submodule.map (LinearMap.inl ℝ V V) (⨆ i, U i) ≤
        ⨆ i, W i := by
      rw [Submodule.map_iSup]
      refine iSup_le fun i ↦ ?_
      rintro z ⟨a, ha, rfl⟩
      exact Submodule.mem_iSup_of_mem i ⟨ha, (U i).zero_mem⟩
    exact hinl ⟨x, hx, by simp⟩
  have hshear : S (x, 0) ∈ ∑ i : Fin m, W i := by
    rw [← hsum]
    exact ⟨(x, 0), hxW, rfl⟩
  have hle : (∑ i : Fin m, W i) ≤ (⨆ i, U i).prod (⨆ i, U i) := by
    rw [hsumW]
    refine iSup_le fun i ↦ ?_
    intro z hz
    exact ⟨le_iSup U i hz.1, le_iSup U i hz.2⟩
  have := (hle hshear).2
  simpa [S] using this
