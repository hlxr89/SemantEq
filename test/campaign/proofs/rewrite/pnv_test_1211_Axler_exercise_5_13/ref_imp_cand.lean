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
theorem dummy {V : Type u_1} [AddCommGroup V] [Module ℂ V] {T : Module.End ℂ V} (hT : ∀ (W : Submodule ℂ V), finrank ℂ W = finrank ℂ V - 1 → ∀ (v : V), v ∈ W → T v ∈ W) : ∃ (c : ℂ), ∀ (v : V), T v = c • v := by
  classical
  have hcol : ∀ v, ¬ LinearIndependent ℂ ![v, T v] := by
    intro v hv
    have hTv : T v ∉ Submodule.span ℂ {v} := by
      intro hmem
      rw [Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have hzero : (-c) • v + (1 : ℂ) • T v = 0 := by
        rw [← hc]
        simp only [one_smul, neg_smul, neg_add_cancel]
      exact one_ne_zero ((LinearIndependent.pair_iff.mp hv) (-c) 1 hzero).2
    obtain ⟨f, hfv, hspan⟩ := Submodule.exists_le_ker_of_notMem hTv
    have hf : f ≠ 0 := by
      intro hf
      rw [hf] at hfv
      exact hfv rfl
    have hrank : finrank ℂ (LinearMap.ker f) = finrank ℂ V - 1 := by
      by_cases hfinite : Module.Finite ℂ V
      · letI := hfinite
        exact Nat.eq_sub_of_add_eq (Module.Dual.finrank_ker_add_one_of_ne_zero hf)
      · have hker : ¬ Module.Finite ℂ (LinearMap.ker f) := by
          intro hkerFinite
          letI := hkerFinite
          letI : Module.Finite ℂ (LinearMap.range f) := inferInstance
          letI : Module.Finite ℂ (V ⧸ LinearMap.ker f) :=
            Module.Finite.of_injective f.quotKerEquivRange.toLinearMap
              f.quotKerEquivRange.injective
          let e := Classical.choice (quotient_prod_linearEquiv (LinearMap.ker f))
          haveI : Module.Finite ℂ ((V ⧸ LinearMap.ker f) × LinearMap.ker f) := inferInstance
          exact hfinite (Module.Finite.of_surjective e.toLinearMap e.surjective)
        rw [Module.finrank_of_not_finite hker, Module.finrank_of_not_finite hfinite]
    have hvker : v ∈ LinearMap.ker f :=
      hspan (Submodule.mem_span_singleton_self v)
    have hTvker := hT (LinearMap.ker f) hrank v hvker
    exact hfv (LinearMap.mem_ker.mp hTvker)
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hcol
  refine ⟨c, fun v ↦ ?_⟩
  rw [hc]
  rfl
