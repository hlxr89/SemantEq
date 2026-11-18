import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {T : V →ₗ[ℝ] V} (h : ∀ (W : Submodule ℝ V), W < (⊤ : Submodule ℝ V) → LinearMap.range T ≤ W → LinearMap.range T ≤ W.map T) : ∃ a : ℝ, T = a • LinearMap.id := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_13 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {T : End F V}
  (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
  Submodule.map T U = U) : ∃ c : F, T = c • LinearMap.id := by
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro v hv
  let s : Set V := Set.range ![v, T v]
  have hs : LinearIndepOn F id s := hv.linearIndepOn_id
  let b := Module.Basis.extend hs
  have hv_mem : v ∈ s := ⟨0, by simp⟩
  have hTv_mem : T v ∈ s := ⟨1, by simp⟩
  let iv : hs.extend (Set.subset_univ s) := ⟨v, hs.subset_extend _ hv_mem⟩
  let iTv : hs.extend (Set.subset_univ s) := ⟨T v, hs.subset_extend _ hTv_mem⟩
  have hi : iv ≠ iTv := by
    intro e
    have : v = T v := congrArg Subtype.val e
    have h01 : (0 : Fin 2) = 1 := hv.injective (by simpa using this)
    have hne : (0 : Fin 2) ≠ 1 := by decide
    exact hne h01
  let f : V →ₗ[F] F := b.coord iTv
  let U : Submodule F V := LinearMap.ker f
  have hbTv : b iTv = T v := by
    simp [b, iTv, Module.Basis.extend_apply_self]
  have hbv : b iv = v := by
    simp [b, iv, Module.Basis.extend_apply_self]
  have hfTv : f (T v) = 1 := by
    rw [← hbTv]
    change b.coord iTv (b iTv) = 1
    simp
  have hfv : f v = 0 := by
    rw [← hbv]
    change b.coord iTv (b iv) = 0
    simp [hi]
  have hf : f ≠ 0 := by
    intro hf
    have := LinearMap.congr_fun hf (T v)
    simp [hfTv] at this
  have hdim : finrank F U = finrank F V - 1 := by
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    change finrank F (LinearMap.ker f) = finrank F V - 1
    omega
  have hvU : v ∈ U := hfv
  have hTvU : T v ∈ U := by
    have hm : T v ∈ Submodule.map T U := ⟨v, hvU, rfl⟩
    rw [hS U hdim] at hm
    exact hm
  exact one_ne_zero (hfTv.symm.trans (show f (T v) = 0 from hTvU))
