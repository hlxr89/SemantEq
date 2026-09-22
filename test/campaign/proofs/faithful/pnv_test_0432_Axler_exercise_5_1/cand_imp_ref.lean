import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {V : Type*} [AddCommGroup V] [Module ℝ V] {T : V →ₗ[ℝ] V} {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, T '' (U i : Set V) ⊆ U i) : T '' ((⨆ i, U i) : Set V) ⊆ (⨆ i, U i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_1 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {L : V →ₗ[F] V} {n : ℕ} (U : Fin n → Submodule F V)
  (hU : ∀ i : Fin n, Submodule.map L (U i) = U i) :
  Submodule.map L (∑ i : Fin n, U i : Submodule F V) =
  (∑ i : Fin n, U i : Submodule F V) := by
  classical
  let Tf : (V →₀ ℝ) →ₗ[ℝ] (V →₀ ℝ) := Finsupp.lmapDomain ℝ ℝ (fun x => L x)
  let Uf : Fin n → Submodule ℝ (V →₀ ℝ) := fun i => Finsupp.supported ℝ ℝ (U i : Set V)
  have hUf : ∀ i, Tf '' (Uf i : Set (V →₀ ℝ)) ⊆ Uf i := by
    intro i
    rintro g ⟨f, hf, rfl⟩
    change (Finsupp.mapDomain (fun x => L x) f).support.toSet ⊆ (U i : Set V)
    intro y hy
    have hy' : y ∈ f.support.image (fun x => L x) := Finsupp.mapDomain_support hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy'
    have hxU : x ∈ U i := hf hx
    have hLx : L x ∈ Submodule.map L (U i) := ⟨x, hxU, rfl⟩
    rwa [hU i] at hLx
  have hsingle : ∀ i (x : V), x ∈ U i → L x ∈ ∑ j : Fin n, U j := by
    intro i x hx
    have hxUf : Finsupp.single x (1 : ℝ) ∈ Uf i := Finsupp.single_mem_supported ℝ (1 : ℝ) hx
    have hxUnion : Finsupp.single x (1 : ℝ) ∈ (⨆ j, (Uf j : Set (V →₀ ℝ))) :=
      Set.mem_iUnion.mpr ⟨i, hxUf⟩
    have hout := dummy_assumed (T := Tf) (U := Uf) hUf ⟨Finsupp.single x (1 : ℝ), hxUnion, rfl⟩
    have hout' : Finsupp.single (L x) (1 : ℝ) ∈ (⨆ j, (Uf j : Set (V →₀ ℝ))) := by
      simpa [Tf] using hout
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hout'
    have hLxU : L x ∈ U j := by
      by_contra hn
      have hz := (Finsupp.mem_supported' ℝ (Finsupp.single (L x) (1 : ℝ))).mp hj (L x) hn
      simpa using hz
    have hjle : U j ≤ ∑ k : Fin n, U k := by
      simpa only [Submodule.add_eq_sup] using
        (Finset.le_sup (f := U) (Finset.mem_univ j) : U j ≤ Finset.univ.sup U)
    exact hjle hLxU
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    simpa only [Submodule.add_eq_sup] using
      (Finset.sup_le (s := Finset.univ) (f := U) (fun i _ x hx => hsingle i x hx) :
        Finset.univ.sup U ≤ Submodule.comap L (∑ i : Fin n, U i))
  · simpa only [Submodule.add_eq_sup] using
      (Finset.sup_le (s := Finset.univ) (f := U) (fun i hi => by
        rw [← hU i]
        exact Submodule.map_mono (by
          simpa only [Submodule.add_eq_sup] using
            (Finset.le_sup (f := U) hi : U i ≤ Finset.univ.sup U))) :
        Finset.univ.sup U ≤ Submodule.map L (∑ i : Fin n, U i))
