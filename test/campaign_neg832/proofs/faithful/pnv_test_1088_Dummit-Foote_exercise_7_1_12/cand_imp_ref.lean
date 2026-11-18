import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type u} [Field F] {R : Type u} [Ring R] (f : R →+* F) (hf1 : f 1 = 1) (hf3 : Function.Surjective f) : IsDomain R := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_7_1_12 {F : Type*} [Field F] {K : Subring F}
  (hK : (1 : F) ∈ K) : IsDomain K := by
  let f : K × F →+* F := RingHom.snd K F
  have hf1 : f 1 = 1 := by
    rfl
  have hf3 : Function.Surjective f := fun y => ⟨(0, y), rfl⟩
  letI : IsDomain (K × F) := dummy_assumed f hf1 hf3
  let g : K →+* K × F := (RingHom.id K).prod K.subtype
  have hg : Function.Injective g := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  exact hg.isDomain g
