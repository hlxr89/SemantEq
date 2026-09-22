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
  obtain ⟨e, he⟩ := exercise_5_13_assumed (F := K) (V := V) (T := LinearMap.id)
    (fun U _ ↦ Submodule.map_id U)
  have hdep : ∀ v : V, ¬ LinearIndependent K ![v, T v] := by
    intro v hv
    have hv0 : v ≠ 0 := hv.ne_zero 0
    have hTv : T v ∉ K ∙ v := by
      rw [Submodule.mem_span_singleton]
      rintro ⟨a, ha⟩
      exact (LinearIndependent.pair_iff' hv0).mp hv a ha
    obtain ⟨f, hfTv, hvf⟩ := Submodule.exists_le_ker_of_notMem hTv
    have hf0 : f ≠ 0 := by
      intro hf
      apply hfTv
      rw [hf]
      rfl
    have hfin : finrank K V - 1 = finrank K (LinearMap.ker f) :=
      Nat.sub_eq_of_eq_add (Module.Dual.finrank_ker_add_one_of_ne_zero hf0).symm
    have hvker : v ∈ LinearMap.ker f := hvf (Submodule.subset_span (by simp))
    have hTvker : T v ∈ LinearMap.ker f := h (LinearMap.ker f) hfin ⟨v, hvker, rfl⟩
    exact hfTv (LinearMap.mem_ker.mp hTvker)
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
  have he' : (1 : End K V) = e • 1 := he
  rw [he'] at ha
  refine ⟨a * e, ?_⟩
  simpa only [smul_smul] using ha
