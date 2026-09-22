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
  have hcol : ∀ v : V, ¬ LinearIndependent ℂ ![v, T v] := by
      intro v hind
      have hnotmem : T v ∉ Submodule.span ℂ {v} := by
        rw [Submodule.mem_span_singleton]
        exact fun ⟨a, ha⟩ ↦ (LinearIndependent.pair_iff' (hind.ne_zero 0)).mp hind a ha
      let q := Submodule.mkQ (Submodule.span ℂ {v})
      have hq : q (T v) ≠ 0 := by
        simpa [q, Submodule.Quotient.mk_eq_zero] using hnotmem
      obtain ⟨g, hg⟩ := Projective.exists_dual_eq_one ℂ hq
      let f : V →ₗ[ℂ] ℂ := g.comp q
      have hfv : f v = 0 := by
        change g (q v) = 0
        rw [show q v = 0 by
          exact (Submodule.Quotient.mk_eq_zero _).2
            (Submodule.subset_span (Set.mem_singleton v))]
        exact g.map_zero
      have hfTv : f (T v) = 1 := by simpa [f] using hg
      let W := LinearMap.ker f
      have hdim : finrank ℂ W = finrank ℂ V - 1 := by
        by_cases hfinite : FiniteDimensional ℂ V
        · letI : FiniteDimensional ℂ V := hfinite
          have hfne : f ≠ 0 := by
            intro hf
            have := LinearMap.congr_fun hf (T v)
            simp [hfTv] at this
          have := Module.Dual.finrank_ker_add_one_of_ne_zero hfne
          change finrank ℂ W + 1 = finrank ℂ V at this
          omega
        · have hWnotfinite : ¬ FiniteDimensional ℂ W := by
            intro hWfinite
            letI : FiniteDimensional ℂ W := hWfinite
            let S : Submodule ℂ V := Submodule.span ℂ {T v}
            haveI : FiniteDimensional ℂ S :=
              FiniteDimensional.span_of_finite (K := ℂ) (Set.finite_singleton (T v))
            haveI : FiniteDimensional ℂ (W ⊔ S : Submodule ℂ V) :=
              Submodule.finiteDimensional_sup W S
            have hsup : W ⊔ S = ⊤ := by
              apply top_unique
              intro x _
              have hxker : x - f x • T v ∈ W := by
                change f (x - f x • T v) = 0
                simp [hfTv]
              have hxspan : f x • T v ∈ S :=
                Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (T v)))
              rw [show x = (x - f x • T v) + f x • T v by abel]
              exact Submodule.add_mem _ (Submodule.mem_sup_left hxker)
                (Submodule.mem_sup_right hxspan)
            haveI : FiniteDimensional ℂ (⊤ : Submodule ℂ V) := hsup ▸ inferInstance
            have : FiniteDimensional ℂ V :=
              LinearMap.finiteDimensional_of_surjective (Submodule.subtype (⊤ : Submodule ℂ V))
                (by simp)
            exact hfinite this
          rw [finrank_of_infinite_dimensional hWnotfinite,
            finrank_of_infinite_dimensional hfinite]
      have hvW : v ∈ W := by simpa [W, LinearMap.mem_ker] using hfv
      have hTvW := hT W hdim v hvW
      have : f (T v) = 0 := by simpa [W, LinearMap.mem_ker] using hTvW
      simp [hfTv] at this
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hcol
  exact ⟨c, fun v ↦ by simpa using LinearMap.congr_fun hc v⟩
