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
  let A : Type := Multiplicative (ZMod 2)
  let B := ULift.{_, 0} A
  refine ⟨B × B, inferInstance, ?_⟩
  let H : Subgroup (B × B) := (MonoidHom.snd B B).ker
  have hH : ∃ H : Subgroup (B × B), H.Normal ∧ ¬ H.Characteristic := by
    refine ⟨H, Subgroup.normal_of_comm H, ?_⟩
    intro hchar
    let a : B := ULift.up (Multiplicative.ofAdd 1)
    have hx : (a, 1) ∈ H := by
      change (1 : B) = 1
      rfl
    have hx' : (a, 1) ∈ Subgroup.comap MulEquiv.prodComm.toMonoidHom H := by
      rw [hchar.fixed MulEquiv.prodComm]
      exact hx
    change a = 1 at hx'
    have ha : a ≠ 1 := by
      intro ha
      have : (1 : ZMod 2) = 0 := by
        simpa [a] using congrArg (fun x : B => x.down.toAdd) ha
      norm_num at this
    exact ha hx'
  exact dummy_assumed (B × B) hH
