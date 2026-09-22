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
    intro v hlin
    have hv0 : v ≠ 0 := hlin.ne_zero 0
    have hTv : T v ∉ F ∙ v := by
      rintro hv
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
      exact ((LinearIndependent.pair_iff' hv0).mp hlin a) ha
    obtain ⟨f, hfTv, hvf⟩ := Submodule.exists_le_ker_of_notMem hTv
    have hf : f ≠ 0 := by
      intro hf
      simp [hf] at hfTv
    have hrank : finrank F (LinearMap.ker f) = finrank F V - 1 := by
      have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf
      omega
    have hvker : v ∈ LinearMap.ker f := hvf (Submodule.subset_span (Set.mem_singleton v))
    have himg : T v ∈ Submodule.map T (LinearMap.ker f) := ⟨v, hvker, rfl⟩
    exact hfTv (show T v ∈ LinearMap.ker f from (hS (LinearMap.ker f) hrank) ▸ himg)
  exact LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hcol
