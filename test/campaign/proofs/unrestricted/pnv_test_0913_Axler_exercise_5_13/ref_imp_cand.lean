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
  have hv0 : v ≠ 0 := by
    intro hvzero
    exact hv.ne_zero 0 (by simpa using hvzero)
  have hTv : T v ∉ K ∙ v := by
    simpa [Submodule.mem_span_singleton] using
      (LinearIndependent.pair_iff' hv0).mp hv
  obtain ⟨f, hfTv, hfspan⟩ :=
    (K ∙ v).exists_dual_map_eq_bot_of_notMem hTv inferInstance
  have hf : f ≠ 0 := by
    intro hf
    simp [hf] at hfTv
  have hdim : finrank K V - 1 = finrank K (LinearMap.ker f) := by
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  have hmem : T v ∈ LinearMap.ker f := by
    apply h (LinearMap.ker f) hdim
    exact ⟨v, by
      change f v = 0
      have : f v ∈ (⊥ : Submodule K K) := by
        rw [← hfspan]
        exact ⟨v, Submodule.mem_span_singleton_self v, rfl⟩
      simpa using this, rfl⟩
  exact hfTv (by simpa [LinearMap.mem_ker] using hmem)
