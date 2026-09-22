import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_13_assumed {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {T : End F V}
  (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
  Submodule.map T U = U) : ∃ c : F, T = c • LinearMap.id := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : End K V) (h : ∀ (U : Subspace K V), finrank K V - 1 = finrank K U → T '' U ≤ U) : ∃ (c : K), T = c • 1 := by
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro v hv
  let p : Submodule K V := K ∙ v
  have hTv : T v ∉ p := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hz : (-a) • v + (1 : K) • T v = 0 := by
      rw [one_smul, ← ha, neg_smul, neg_add_cancel]
    have := hv.eq_zero_of_pair hz
    exact one_ne_zero this.2
  obtain ⟨f, hfp, hfTv⟩ := LinearMap.exists_extend_of_notMem (0 : p →ₗ[K] K) hTv 1
  have hfv : f v = 0 := by
    have hvp : v ∈ p := Submodule.mem_span_singleton.mpr ⟨1, one_smul K v⟩
    have := DFunLike.congr_fun hfp ⟨v, hvp⟩
    simpa using this
  have hf : f ≠ 0 := by
    intro hf
    simp [hf] at hfTv
  have hdim : finrank K V - 1 = finrank K (LinearMap.ker f) := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  have hinv := h (LinearMap.ker f) hdim
  have hTmem : T v ∈ LinearMap.ker f := hinv ⟨v, hfv, rfl⟩
  rw [LinearMap.mem_ker, hfTv] at hTmem
  exact one_ne_zero hTmem
