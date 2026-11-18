import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p a : ℕ} (hp : p.Prime) (h : p = 4 * a + 1) : IsPrimitiveRoot (-a : ℤ) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  have hnZ (x : ZMod p) : ¬ IsPrimitiveRoot x p := by
    intro hx
    apply hx.ne_one hp0.one_lt
    rw [← ZMod.pow_card x, hx.pow_eq_one]
  have hnPos : ¬ IsPrimitiveRoot t p := by
    intro ht
    have hu : IsUnit t := ht.isUnit hp0.ne_zero
    rw [Nat.isUnit_iff] at hu
    exact ht.ne_one hp0.one_lt hu
  have hnNeg : ¬ IsPrimitiveRoot (-t : ℤ) p := by
    intro ht
    have hu : IsUnit (-t : ℤ) := ht.isUnit hp0.ne_zero
    rw [Int.isUnit_iff] at hu
    rcases hu with ht1 | ht1
    · omega
    · have htt : t = 1 := by omega
      subst t
      norm_num at hp1
      subst p
      have hord : orderOf (-1 : ℤ) = 2 := by norm_num [orderOf_neg_one]
      have : (5 : ℕ) = 2 := ht.eq_orderOf.trans hord
      omega
  calc
    IsPrimitiveRoot a p ↔ IsPrimitiveRoot t p :=
      ⟨fun ha ↦ (hnZ _ ha).elim, fun ht ↦ (hnPos ht).elim⟩
    _ ↔ IsPrimitiveRoot (-t : ℤ) p :=
      (dummy_assumed hp0 hp1).symm
    _ ↔ IsPrimitiveRoot (-a) p :=
      ⟨fun ht ↦ (hnNeg ht).elim, fun ha ↦ (hnZ _ ha).elim⟩
