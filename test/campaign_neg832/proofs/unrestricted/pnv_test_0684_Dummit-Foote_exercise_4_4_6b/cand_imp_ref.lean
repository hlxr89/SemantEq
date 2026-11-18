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
  let C := Multiplicative (ZMod 2)
  let B := C × C
  let G : Type _ := ULift B
  let H₀ : Subgroup B := (⊤ : Subgroup C).prod (⊥ : Subgroup C)
  let H : Subgroup G := H₀.comap MulEquiv.ulift.toMonoidHom
  refine ⟨G, inferInstance, H, ?_, ?_⟩
  · infer_instance
  · intro hchar
    let swap : B ≃* B := MulEquiv.prodComm
    let e : G ≃* G := MulEquiv.ulift.trans (swap.trans MulEquiv.ulift.symm)
    have hfixed := hchar.fixed e
    let x : G := ULift.up
      ((Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (0 : ZMod 2)) : B)
    have hx : x ∈ H := by
      change ((Multiplicative.ofAdd (1 : ZMod 2),
        Multiplicative.ofAdd (0 : ZMod 2)) : B) ∈ H₀
      apply Subgroup.mem_prod.mpr
      constructor <;> simp [H₀]
    have hx' : x ∈ H.comap e.toMonoidHom := by
      rw [hfixed]
      exact hx
    change ((Multiplicative.ofAdd (0 : ZMod 2),
      Multiplicative.ofAdd (1 : ZMod 2)) : B) ∈ H₀ at hx'
    have hbad : Multiplicative.ofAdd (1 : ZMod 2) ∈ (⊥ : Subgroup C) :=
      (Subgroup.mem_prod.mp hx').2
    have : (1 : ZMod 2) = 0 := by
      simpa using hbad
    norm_num at this
