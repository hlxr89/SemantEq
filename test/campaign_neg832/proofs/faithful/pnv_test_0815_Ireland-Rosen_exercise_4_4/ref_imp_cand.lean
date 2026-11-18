import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_4_assumed {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {p a : ℕ} (hp : p.Prime) (h : p = 4 * a + 1) : IsPrimitiveRoot (-a : ℤ) p ↔ IsPrimitiveRoot a p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnZ (x : ZMod p) : ¬ IsPrimitiveRoot x p := by
    intro hx
    apply hx.ne_one hp.one_lt
    rw [← ZMod.pow_card x, hx.pow_eq_one]
  have hnPos : ¬ IsPrimitiveRoot a p := by
    intro ha
    have hu : IsUnit a := ha.isUnit hp.ne_zero
    rw [Nat.isUnit_iff] at hu
    exact ha.ne_one hp.one_lt hu
  have hnNeg : ¬ IsPrimitiveRoot (-a : ℤ) p := by
    intro ha
    have hu : IsUnit (-a : ℤ) := ha.isUnit hp.ne_zero
    rw [Int.isUnit_iff] at hu
    rcases hu with ha1 | ha1
    · omega
    · have hat : a = 1 := by omega
      subst a
      norm_num at h
      subst p
      have hord : orderOf (-1 : ℤ) = 2 := by norm_num [orderOf_neg_one]
      have : (5 : ℕ) = 2 := ha.eq_orderOf.trans hord
      omega
  calc
    IsPrimitiveRoot (-a : ℤ) p ↔ IsPrimitiveRoot (-(a : ZMod p)) p :=
      ⟨fun ha ↦ (hnNeg ha).elim, fun ha ↦ (hnZ _ ha).elim⟩
    _ ↔ IsPrimitiveRoot (a : ZMod p) p :=
      (exercise_4_4_assumed hp h (a : ZMod p)).symm
    _ ↔ IsPrimitiveRoot a p :=
      ⟨fun ha ↦ (hnZ _ ha).elim, fun ha ↦ (hnPos ha).elim⟩
