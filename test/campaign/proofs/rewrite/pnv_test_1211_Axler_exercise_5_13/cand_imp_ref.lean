import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {V : Type u_1} [AddCommGroup V] [Module ℂ V] {T : Module.End ℂ V} (hT : ∀ (W : Submodule ℂ V), finrank ℂ W = finrank ℂ V - 1 → ∀ (v : V), v ∈ W → T v ∈ W) : ∃ (c : ℂ), ∀ (v : V), T v = c • v := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_13 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {T : End F V}
  (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
  Submodule.map T U = U) : ∃ c : F, T = c • LinearMap.id := by
  classical
  have hcol : ∀ v, ¬ LinearIndependent F ![v, T v] := by
    intro v hv
    have hTv : T v ∉ Submodule.span F {v} := by
      intro hmem
      rw [Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have hzero : (-c) • v + (1 : F) • T v = 0 := by
        rw [← hc]
        simp only [one_smul, neg_smul, neg_add_cancel]
      exact one_ne_zero ((LinearIndependent.pair_iff.mp hv) (-c) 1 hzero).2
    obtain ⟨f, hfv, hspan⟩ := Submodule.exists_le_ker_of_notMem hTv
    have hf : f ≠ 0 := by
      intro hf
      rw [hf] at hfv
      exact hfv rfl
    have hrank : finrank F (LinearMap.ker f) = finrank F V - 1 :=
      Nat.eq_sub_of_add_eq (Module.Dual.finrank_ker_add_one_of_ne_zero hf)
    have hvker : v ∈ LinearMap.ker f :=
      hspan (Submodule.mem_span_singleton_self v)
    have hmap : Submodule.map T (LinearMap.ker f) = LinearMap.ker f :=
      hS (LinearMap.ker f) hrank
    have hTvker : T v ∈ LinearMap.ker f := by
      rw [← hmap]
      exact ⟨v, hvker, rfl⟩
    exact hfv (LinearMap.mem_ker.mp hTvker)
  exact LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hcol
