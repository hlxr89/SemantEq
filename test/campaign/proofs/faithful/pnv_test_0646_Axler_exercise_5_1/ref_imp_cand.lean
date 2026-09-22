import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_1_assumed {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {L : V →ₗ[F] V} {n : ℕ} (U : Fin n → Submodule F V)
  (hU : ∀ i : Fin n, Submodule.map L (U i) = U i) :
  Submodule.map L (∑ i : Fin n, U i : Submodule F V) =
  (∑ i : Fin n, U i : Submodule F V) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {V : Type*} [AddCommGroup V] [Module ℝ V] {T : V →ₗ[ℝ] V} {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, T '' (U i).carrier ⊆ (U i).carrier) : T '' (Submodule.span ℝ (⋃ i, (U i).carrier)) ⊆ (Submodule.span ℝ (⋃ i, (U i).carrier)) := by
  classical
  let shear : (V × V) →ₗ[ℝ] (V × V) :=
    { toFun := fun p => (p.1, p.2 + T p.1)
      map_add' := by
        intro x y
        ext
        · rfl
        · change x.2 + y.2 + T (x.1 + y.1) =
            (x.2 + T x.1) + (y.2 + T y.1)
          rw [map_add]
          abel
      map_smul' := by
        intro c x
        ext <;> simp [map_smul] }
  let P : Fin m → Submodule ℝ (V × V) := fun i => (U i).prod (U i)
  have hP : ∀ i : Fin m, Submodule.map shear (P i) = P i := by
    intro i
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp.1, (U i).add_mem hp.2 (hU i ⟨p.1, hp.1, rfl⟩)⟩
    · intro hz
      refine ⟨(z.1, z.2 - T z.1), ?_, ?_⟩
      · exact ⟨hz.1, (U i).sub_mem hz.2 (hU i ⟨z.1, hz.1, rfl⟩)⟩
      · simp [shear]
  have htransport := exercise_5_1_assumed P hP
  have hsum : (∑ i : Fin m, P i : Submodule ℝ (V × V)) = ⨆ i, P i := by
    have aux : ∀ s : Finset (Fin m),
        (∑ i ∈ s, P i : Submodule ℝ (V × V)) = s.sup P := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Submodule.add_eq_sup, ih, Finset.sup_insert]
    rw [show (∑ i : Fin m, P i : Submodule ℝ (V × V)) = Finset.univ.sup P by
      simpa using aux Finset.univ]
    exact Finset.sup_univ_eq_iSup P
  rintro y ⟨x, hx, rfl⟩
  have hxP : (x, 0) ∈ (⨆ i, P i) := by
    refine Submodule.span_induction
      (p := fun z _ => (z, 0) ∈ (⨆ i, P i)) ?_ ?_ ?_ ?_ hx
    · intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨i, hi⟩ := hz
      exact Submodule.mem_iSup_of_mem i ⟨hi, (U i).zero_mem⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      simpa using Submodule.add_mem _ ha hb
    · intro c z _ hpair
      simpa using Submodule.smul_mem _ c hpair
  have hsx : shear (x, 0) ∈ (⨆ i, P i) := by
    rw [← hsum, ← htransport]
    exact Submodule.mem_map_of_mem (hsum.symm ▸ hxP)
  have hle : (⨆ i, P i) ≤
      (Submodule.span ℝ (⋃ i, (U i).carrier)).prod
        (Submodule.span ℝ (⋃ i, (U i).carrier)) := by
    refine iSup_le fun i z hz => ⟨?_, ?_⟩
    · exact Submodule.subset_span (Set.mem_iUnion_of_mem i hz.1)
    · exact Submodule.subset_span (Set.mem_iUnion_of_mem i hz.2)
  have := (hle hsx).2
  simpa [shear] using this
