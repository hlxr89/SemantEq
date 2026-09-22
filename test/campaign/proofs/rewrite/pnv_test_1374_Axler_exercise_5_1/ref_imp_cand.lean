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
  let S : (V × V) →ₗ[ℝ] (V × V) :=
    { toFun := fun x ↦ (T x.1 + x.2, x.1)
      map_add' := by
        intro x y
        apply Prod.ext
        · simp only [Prod.fst_add, Prod.snd_add, map_add]
          ac_rfl
        · rfl
      map_smul' := by
        intro c x
        apply Prod.ext
        · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add]
          simp only [RingHom.id_apply]
        · rfl }
  let W : Fin m → Submodule ℝ (V × V) := fun i ↦ (U i).prod (U i)
  have hW : ∀ i : Fin m, Submodule.map S (W i) = W i := by
    intro i
    apply le_antisymm
    · rintro z ⟨x, hx, rfl⟩
      exact ⟨(U i).add_mem ((hU i) ⟨x.1, hx.1, rfl⟩) hx.2, hx.1⟩
    · rintro z ⟨hz₁, hz₂⟩
      refine ⟨(z.2, z.1 - T z.2), ?_, ?_⟩
      · exact ⟨hz₂, (U i).sub_mem hz₁ ((hU i) ⟨z.2, hz₂, rfl⟩)⟩
      · apply Prod.ext
        · change T z.2 + (z.1 - T z.2) = z.1
          rw [add_comm, sub_add_cancel]
        · rfl
  have hsumW : (∑ i : Fin m, W i : Submodule ℝ (V × V)) = ⨆ i, W i := by
    simpa only [Submodule.add_eq_sup] using (Finset.sup_univ_eq_iSup W)
  have hS : Submodule.map S (⨆ i, W i) = ⨆ i, W i := by
    rw [← hsumW]
    exact exercise_5_1_assumed W hW
  rintro x ⟨a, ha, rfl⟩
  have hinl : Submodule.map (LinearMap.inl ℝ V V) (⨆ i, U i) ≤ ⨆ i, W i := by
    rw [Submodule.map_iSup]
    refine iSup_le fun i ↦ ?_
    refine le_trans ?_ (le_iSup W i)
    rintro z ⟨y, hy, rfl⟩
    exact ⟨hy, (U i).zero_mem⟩
  have haW : (a, 0) ∈ ⨆ i, W i := by
    apply hinl
    exact ⟨a, ha, rfl⟩
  have hSa : S (a, 0) ∈ ⨆ i, W i := by
    rw [← hS]
    exact ⟨(a, 0), haW, rfl⟩
  have hproj : Submodule.map (LinearMap.fst ℝ V V) (⨆ i, W i) ≤ ⨆ i, U i := by
    rw [Submodule.map_iSup]
    refine iSup_le fun i ↦ ?_
    rintro y ⟨z, hz, rfl⟩
    exact Submodule.mem_iSup_of_mem i hz.1
  apply hproj
  refine ⟨S (a, 0), hSa, ?_⟩
  change T a + 0 = T a
  exact add_zero (T a)
