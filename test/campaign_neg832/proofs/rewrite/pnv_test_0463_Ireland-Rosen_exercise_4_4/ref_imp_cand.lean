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
theorem dummy {p : ℕ} [hp : Fact p.Prime] (hp4 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have hp2 : p ≠ 2 := by
    intro h
    have hmod : 2 % 4 = 1 := h ▸ hp4
    change (2 : ℕ) = 1 at hmod
    exact (Nat.succ_ne_self 1) hmod
  have hint (x : ℤ) : ¬IsPrimitiveRoot x p := by
    intro hx
    rcases Int.isUnit_iff.mp (hx.isUnit hp.out.ne_zero) with rfl | rfl
    · exact hp.out.ne_one (hx.unique IsPrimitiveRoot.one)
    · exact hp2 (hx.unique (IsPrimitiveRoot.neg_one 0 (Nat.zero_lt_succ 1).ne))
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  have hzmod (x : ZMod p) : ¬IsPrimitiveRoot x p := by
    intro hx
    exact hx.neZero'.out (ZMod.natCast_self p)
  have hleft : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (a : ZMod p) p :=
    iff_of_false (hint a) (hzmod (a : ZMod p))
  have hright : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot (-(a : ZMod p)) p :=
    iff_of_false (hint (-a)) (hzmod (-(a : ZMod p)))
  have hp1 : p = 4 * (p / 4) + 1 := by
    simpa only [hp4, Nat.add_comm] using (Nat.mod_add_div p 4).symm
  rw [hleft, hright]
  exact exercise_4_4_assumed hp.out hp1 (a : ZMod p)
