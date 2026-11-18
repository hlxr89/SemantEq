import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (hG : ∃ H : Subgroup G, H.Normal ∧ ¬ H.Characteristic) : ∃ H : Subgroup G, H.Normal ∧ ¬ H.Characteristic := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := by
  let B := Multiplicative ℤ × Multiplicative ℤ
  let HB : Subgroup B := Subgroup.prod ⊤ ⊥
  refine ⟨ULift B, inferInstance, HB.comap MulEquiv.ulift.toMonoidHom, inferInstance, ?_⟩
  intro h
  let e : ULift B ≃* B := MulEquiv.ulift
  let phi : ULift B ≃* ULift B := e.trans ((MulEquiv.prodComm : B ≃* B).trans e.symm)
  have heq := h.fixed phi
  let a : Multiplicative ℤ := Multiplicative.ofAdd 1
  let x : ULift B := e.symm (a, 1)
  have hxH : x ∈ HB.comap e.toMonoidHom := by
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
  have hxC : x ∈ (HB.comap e.toMonoidHom).comap phi.toMonoidHom := by
    rw [heq]
    exact hxH
  dsimp [phi, x, e] at hxC
  have ha : a ∈ (⊥ : Subgroup (Multiplicative ℤ)) := (Subgroup.mem_prod.mp hxC).2
  have ha' : a = 1 := Subgroup.mem_bot.mp ha
  norm_num [a] at ha'
