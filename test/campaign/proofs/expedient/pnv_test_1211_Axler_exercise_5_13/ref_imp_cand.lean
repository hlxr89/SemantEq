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
    intro v hlin
    have hv0 : v ≠ 0 := hlin.ne_zero 0
    have hTv : T v ∉ ℂ ∙ v := by
      rintro hv
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
      exact ((LinearIndependent.pair_iff' hv0).mp hlin a) ha
    obtain ⟨f, hfTv, hvf⟩ := Submodule.exists_le_ker_of_notMem hTv
    have hf : f ≠ 0 := by
      intro hf
      simp [hf] at hfTv
    have hrank : finrank ℂ (LinearMap.ker f) = finrank ℂ V - 1 := by
      by_cases hfd : FiniteDimensional ℂ V
      · letI := hfd
        have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf
        omega
      · have hker : ¬ FiniteDimensional ℂ (LinearMap.ker f) := by
          intro hk
          letI := hk
          let u : V := (f (T v))⁻¹ • T v
          have hfu : f u = 1 := by simp [u, hfTv]
          let g : (LinearMap.ker f × ℂ) →ₗ[ℂ] V :=
            LinearMap.coprod (LinearMap.ker f).subtype (LinearMap.toSpanSingleton ℂ V u)
          have hg : Function.Surjective g := by
            intro x
            refine ⟨(⟨x - f x • u, ?_⟩, f x), ?_⟩
            · simp [LinearMap.mem_ker, hfu]
            · simp [g]
          exact hfd (FiniteDimensional.of_surjective g hg)
        rw [finrank_of_infinite_dimensional hker,
          finrank_of_infinite_dimensional hfd]
    have hvker : v ∈ LinearMap.ker f := hvf (Submodule.subset_span (Set.mem_singleton v))
    have := hT (LinearMap.ker f) hrank v hvker
    exact hfTv this
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hcol
  refine ⟨c, fun v ↦ ?_⟩
  simpa using LinearMap.congr_fun hc v
