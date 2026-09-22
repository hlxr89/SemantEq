import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_3_7_assumed {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {F K : Type*} [Field F] [Field K] [Algebra F K] {a : K} (ha2 : IsAlgebraic F (a^2)) : IsAlgebraic F a := by
  let S : Subfield K := (algebraMap F K).fieldRange
  let f : F →+* S := (algebraMap F K).codRestrict S (fun x => ⟨x, rfl⟩)
  letI : Algebra F S := f.toAlgebra
  have hmap : ∀ x : F, algebraMap F K x = algebraMap S K (algebraMap F S x) := by
    intro x
    rfl
  letI : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq hmap
  have haS : IsAlgebraic S (a ^ 2) := ha2.tower_top S
  have hS : IsAlgebraic S a := exercise_5_3_7_assumed haS
  let e : F ≃+* S := RingEquiv.ofBijective f ⟨RingHom.injective f, fun x => by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨y, Subtype.ext hy⟩⟩
  have hFS : Algebra.IsAlgebraic F S := by
    exact ⟨fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      exact isAlgebraic_algebraMap (R := F) (A := S) y⟩
  letI : Algebra.IsAlgebraic F S := hFS
  exact hS.restrictScalars F
