import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact p.Prime] (h : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  have hmod : p % 4 = 1 := by
    rw [hp1, Nat.add_mod, Nat.mul_mod, Nat.mod_self]
    simp only [zero_mul, Nat.zero_mod, zero_add, Nat.one_mod]
  have hcand := dummy_assumed hmod (a.val : ℤ)
  have int_no_root (z : ℤ) : ¬ IsPrimitiveRoot z p := by
    intro hz
    rcases (pow_eq_one_iff_of_ne_zero hp0.ne_zero).mp hz.pow_eq_one with hz1 | ⟨hzneg, heven⟩
    · have hp_eq_one : p = 1 := by
        rw [hz1] at hz
        exact hz.unique IsPrimitiveRoot.one
      exact hp0.ne_one hp_eq_one
    · have hp_eq_two : p = 2 := hp0.even_iff.mp heven
      rw [hp_eq_two] at hmod
      change 2 = 1 at hmod
      exact OfNat.one_ne_ofNat 2 hmod.symm
  have zmod_no_root (z : ZMod p) : ¬ IsPrimitiveRoot z p := by
    intro hz
    have hz1 : z = 1 := by
      rw [← ZMod.pow_card z, hz.pow_eq_one]
    rw [hz1] at hz
    exact hp0.ne_one (hz.unique IsPrimitiveRoot.one)
  have hpos : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (a.val : ℤ) p := by
    exact ⟨fun ha ↦ (zmod_no_root a ha).elim, fun ha ↦ (int_no_root (a.val : ℤ) ha).elim⟩
  have hneg : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot (-(a.val : ℤ)) p := by
    exact ⟨fun ha ↦ (zmod_no_root (-a) ha).elim,
      fun ha ↦ (int_no_root (-(a.val : ℤ)) ha).elim⟩
  rw [hpos, hneg]
  exact hcand
