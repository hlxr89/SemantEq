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
  have hcol : ∀ x : V, ¬ LinearIndependent K ![x, T x] := by
    intro x hx
    have hnot : T x ∉ Submodule.span K {x} := by
      rw [Submodule.mem_span_singleton]
      push_neg
      exact (LinearIndependent.pair_iff' (hx.ne_zero 0)).mp hx
    obtain ⟨f, hfx, hker⟩ := Submodule.exists_le_ker_of_notMem hnot
    have hf : f ≠ 0 := by
      intro hf
      simp [hf] at hfx
    have hdim : finrank K V - 1 = finrank K (LinearMap.ker f) := by
      have hadd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
      omega
    have hxker : x ∈ LinearMap.ker f := hker (Submodule.subset_span (by simp))
    have hTx : T x ∈ LinearMap.ker f := h (LinearMap.ker f) hdim ⟨x, hxker, rfl⟩
    exact hfx hTx
  by_cases hT : Function.Injective T
  · obtain ⟨c, hc⟩ := exercise_5_13_assumed (T := T) (fun U hU ↦ by
      have hle : Submodule.map T U ≤ U := by
        rintro y ⟨x, hx, rfl⟩
        exact h U hU.symm ⟨x, hx, rfl⟩
      apply Submodule.eq_of_le_of_finrank_eq hle
      rw [← LinearMap.range_domRestrict]
      exact LinearMap.finrank_range_of_inj (hT.comp U.subtype_injective))
    exact ⟨c, by simpa using hc⟩
  · have hsub_inj : Function.Injective (T - (LinearMap.id : End K V)) := by
      rw [← LinearMap.ker_eq_bot]
      apply bot_unique
      intro y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy
      rw [Submodule.mem_bot]
      by_contra hy0
      have hker_ne : LinearMap.ker T ≠ ⊥ := by
        intro hker
        exact hT (LinearMap.ker_eq_bot.mp hker)
      obtain ⟨x, hxker, hx⟩ := (LinearMap.ker T).ne_bot_iff.mp hker_ne
      have hxy : LinearIndependent K ![x, y] := by
        apply (LinearIndependent.pair_iff' hx).mpr
        intro a ha
        have hTy0 : T y = 0 := by
          rw [← ha]
          simp [LinearMap.mem_ker.mp hxker]
        exact hy0 (hy.symm.trans hTy0)
      apply (hcol (x + y))
      simpa [LinearMap.mem_ker.mp hxker, hy] using
        (LinearIndependent.pair_add_left_iff (R := K) (x := x) (y := y)).mpr hxy
    obtain ⟨c, hc⟩ := exercise_5_13_assumed (T := T - (LinearMap.id : End K V)) (fun U hU ↦ by
      have hle : Submodule.map (T - (LinearMap.id : End K V)) U ≤ U := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact U.sub_mem (h U hU.symm ⟨x, hx, rfl⟩) hx
      apply Submodule.eq_of_le_of_finrank_eq hle
      rw [← LinearMap.range_domRestrict]
      exact LinearMap.finrank_range_of_inj (hsub_inj.comp U.subtype_injective))
    refine ⟨c + 1, ?_⟩
    rw [show T = (T - (LinearMap.id : End K V)) + LinearMap.id by abel, hc]
    ext x
    simp [add_smul]
