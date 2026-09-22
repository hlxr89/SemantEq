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
theorem dummy {V : Type*} [AddCommGroup V] [Module ℝ V] (T : End ℝ V) {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, (U i).map T ≤ U i) : (Submodule.span ℝ (⋃ i, (U i : Set V))).map T ≤ Submodule.span ℝ (⋃ i, (U i : Set V)) := by
  let fst : V × V →ₗ[ℝ] V := LinearMap.fst ℝ V V
  let snd : V × V →ₗ[ℝ] V := LinearMap.snd ℝ V V
  let S : V × V →ₗ[ℝ] V × V := fst.prod (T.comp fst + snd)
  let Sinv : V × V →ₗ[ℝ] V × V := fst.prod (snd - T.comp fst)
  let e : V →ₗ[ℝ] V × V := LinearMap.inl ℝ V V
  let P : Submodule ℝ V := ∑ i, U i
  let Q : Submodule ℝ (V × V) := ∑ i, (U i).prod (U i)
  have hsum : (∑ i, U i) = ⨆ i, U i := by
    rw [← Finset.sup_univ_eq_iSup]
    generalize (Finset.univ : Finset (Fin m)) = s
    induction s using Finset.induction_on with
    | empty => simp [Submodule.zero_eq_bot]
    | @insert a s ha ih => simp [ha, ih, Submodule.add_eq_sup]
  have hsumProd : (∑ i, (U i).prod (U i)) = ⨆ i, (U i).prod (U i) := by
    rw [← Finset.sup_univ_eq_iSup]
    generalize (Finset.univ : Finset (Fin m)) = s
    induction s using Finset.induction_on with
    | empty => simp [Submodule.zero_eq_bot]
    | @insert a s ha ih => simp [ha, ih, Submodule.add_eq_sup]
  have hUi : ∀ i, Submodule.map S ((U i).prod (U i)) = (U i).prod (U i) := by
    intro i
    apply le_antisymm
    · rintro z ⟨w, hw, rfl⟩
      have hw' := (Submodule.mem_prod).mp hw
      apply (Submodule.mem_prod).mpr
      refine ⟨?_, ?_⟩
      · simpa [S, fst] using hw'.1
      · simpa [S, fst, snd] using (U i).add_mem (hU i ⟨w.1, hw'.1, rfl⟩) hw'.2
    · intro z hz
      have hz' := (Submodule.mem_prod).mp hz
      refine ⟨Sinv z, ?_, ?_⟩
      · apply (Submodule.mem_prod).mpr
        refine ⟨?_, ?_⟩
        · simpa [Sinv, fst] using hz'.1
        · simpa [Sinv, fst, snd] using (U i).sub_mem hz'.2 (hU i ⟨z.1, hz'.1, rfl⟩)
      · ext <;> simp [S, Sinv, fst, snd]
  have hSQ : Submodule.map S Q = Q := by
    exact exercise_5_1_assumed (fun i => (U i).prod (U i)) hUi
  have he : Submodule.map e P ≤ Q := by
    rw [show P = ∑ i, U i from rfl, hsum, Submodule.map_iSup,
      show Q = ∑ i, (U i).prod (U i) from rfl, hsumProd]
    refine iSup_le fun i => ?_
    refine le_trans ?_ (le_iSup (fun i => (U i).prod (U i)) i)
    rintro z ⟨x, hx, rfl⟩
    apply (Submodule.mem_prod).mpr
    simpa [e] using And.intro hx (Submodule.zero_mem (U i))
  have hsnd : Submodule.map snd Q ≤ P := by
    rw [show Q = ∑ i, (U i).prod (U i) from rfl, hsumProd, Submodule.map_iSup,
      show P = ∑ i, U i from rfl, hsum]
    refine iSup_le fun i => ?_
    refine le_trans ?_ (le_iSup U i)
    rintro z ⟨x, hx, rfl⟩
    exact (Submodule.mem_prod).mp hx |>.2
  rw [← Submodule.iSup_eq_span, ← hsum]
  rintro z ⟨x, hx, rfl⟩
  have hex : e x ∈ Q := he ⟨x, hx, rfl⟩
  have hSx : S (e x) ∈ Q := by
    rw [← hSQ]
    exact ⟨e x, hex, rfl⟩
  have hout : snd (S (e x)) ∈ P := hsnd ⟨S (e x), hSx, rfl⟩
  simpa [S, e, fst, snd] using hout
