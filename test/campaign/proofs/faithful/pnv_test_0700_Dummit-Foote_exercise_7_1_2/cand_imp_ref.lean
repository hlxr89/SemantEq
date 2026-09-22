import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] (u : R) (hu : IsUnit u) : IsUnit (-u) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_7_1_2 {R : Type*} [Ring R] {u : R}
  (hu : IsUnit u) : IsUnit (-u) := by
  let a : Rˣ := hu.unit
  let S : Subring R := Subring.closure ({(a : R), (↑(a⁻¹) : R)} : Set R)
  letI : CommRing S := Subring.closureCommRingOfComm (by
    rintro x (rfl | rfl) y (rfl | rfl)
    · rfl
    · exact a.val_inv.trans a.inv_val.symm
    · exact a.inv_val.trans a.val_inv.symm
    · rfl)
  let x : S := ⟨(a : R), Subring.subset_closure (by simp)⟩
  have hx : IsUnit x := by
    refine ⟨{
      val := x
      inv := ⟨↑(a⁻¹), Subring.subset_closure (by simp)⟩
      val_inv := ?_
      inv_val := ?_ }, rfl⟩
    · ext
      simp [x]
    · ext
      simp [x]
  have hneg : IsUnit (-x) := dummy_assumed x hx
  have hmapped := hneg.map S.subtype
  simpa [x, a, hu.unit_spec] using hmapped
