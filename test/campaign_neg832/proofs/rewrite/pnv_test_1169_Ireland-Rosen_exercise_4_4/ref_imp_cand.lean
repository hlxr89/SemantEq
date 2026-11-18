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
theorem dummy {p : ℕ} [hp : Fact p.Prime] (h : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have hp1 : p = 4 * (p / 4) + 1 := by
    have hdiv := Nat.mod_add_div p 4
    rw [h] at hdiv
    rw [← Nat.add_comm]
    exact hdiv.symm
  have href := exercise_4_4_assumed hp.out hp1 (a : ZMod p)
  have int_no_root (z : ℤ) : ¬ IsPrimitiveRoot z p := by
    intro hz
    rcases (pow_eq_one_iff_of_ne_zero hp.out.ne_zero).mp hz.pow_eq_one with hz1 | ⟨hzneg, heven⟩
    · have hp_eq_one : p = 1 := by
        rw [hz1] at hz
        exact hz.unique IsPrimitiveRoot.one
      exact hp.out.ne_one hp_eq_one
    · have hp_eq_two : p = 2 := hp.out.even_iff.mp heven
      rw [hp_eq_two] at h
      change 2 = 1 at h
      exact OfNat.one_ne_ofNat 2 h.symm
  have zmod_no_root (z : ZMod p) : ¬ IsPrimitiveRoot z p := by
    intro hz
    have hz1 : z = 1 := by
      rw [← ZMod.pow_card z, hz.pow_eq_one]
    rw [hz1] at hz
    exact hp.out.ne_one (hz.unique IsPrimitiveRoot.one)
  have hpos : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (a : ZMod p) p := by
    exact ⟨fun ha ↦ (int_no_root a ha).elim, fun ha ↦ (zmod_no_root (a : ZMod p) ha).elim⟩
  have hneg : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot (-(a : ZMod p)) p := by
    exact ⟨fun ha ↦ (int_no_root (-a) ha).elim,
      fun ha ↦ (zmod_no_root (-(a : ZMod p)) ha).elim⟩
  rw [hpos, hneg]
  exact href
