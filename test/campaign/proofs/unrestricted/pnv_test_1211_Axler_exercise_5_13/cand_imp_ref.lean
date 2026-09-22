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
  have hcol : ∀ v : V, ¬ LinearIndependent F ![v, T v] := by
    intro v hind
    have hnotmem : T v ∉ Submodule.span F {v} := by
      rw [Submodule.mem_span_singleton]
      exact fun ⟨a, ha⟩ ↦ (LinearIndependent.pair_iff' (hind.ne_zero 0)).mp hind a ha
    let q := Submodule.mkQ (Submodule.span F {v})
    have hq : q (T v) ≠ 0 := by
      simpa [q, Submodule.Quotient.mk_eq_zero] using hnotmem
    obtain ⟨g, hg⟩ := Projective.exists_dual_eq_one F hq
    let f : V →ₗ[F] F := g.comp q
    have hfv : f v = 0 := by
      change g (q v) = 0
      rw [show q v = 0 by
        exact (Submodule.Quotient.mk_eq_zero _).2
          (Submodule.subset_span (Set.mem_singleton v))]
      exact g.map_zero
    have hfTv : f (T v) = 1 := by simpa [f] using hg
    have hfne : f ≠ 0 := by
      intro hf
      have := LinearMap.congr_fun hf (T v)
      simp [hfTv] at this
    let W := LinearMap.ker f
    have hsum := Module.Dual.finrank_ker_add_one_of_ne_zero hfne
    have hdim : finrank F W = finrank F V - 1 := by
      change finrank F W + 1 = finrank F V at hsum
      omega
    have hvW : v ∈ W := by simpa [W, LinearMap.mem_ker] using hfv
    have himage : T v ∈ Submodule.map T W := ⟨v, hvW, rfl⟩
    have hTvW : T v ∈ W := by simpa [hS W hdim] using himage
    have : f (T v) = 0 := by simpa [W, LinearMap.mem_ker] using hTvW
    simp [hfTv] at this
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hcol
  exact ⟨c, hc⟩
