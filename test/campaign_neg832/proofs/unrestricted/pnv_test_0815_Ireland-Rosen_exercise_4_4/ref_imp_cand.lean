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
  have hp_odd : Odd p := by
    rw [h]
    exact ⟨2 * a, by omega⟩
  have not_primitive_int (x : ℤ) : ¬IsPrimitiveRoot x p := by
    intro hx
    rcases hx.isUnit hp.ne_zero with ⟨u, rfl⟩
    rcases Int.units_eq_one_or u with hu | hu
    · subst u
      exact hx.ne_one hp.one_lt rfl
    · subst u
      have bad : (-1 : ℤ) = 1 := by
        simpa [hp_odd.neg_one_pow] using hx.pow_eq_one
      norm_num at bad
  have not_primitive_nat (x : ℕ) : ¬IsPrimitiveRoot x p := by
    intro hx
    have hx_one : x = 1 :=
      (pow_eq_one_iff.mp hx.pow_eq_one).resolve_right hp.ne_zero
    exact hx.ne_one hp.one_lt hx_one
  constructor
  · intro hneg
    exact (not_primitive_int (-a : ℤ) hneg).elim
  · intro hpos
    exact (not_primitive_nat a hpos).elim
