import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact p.Prime] (hp4 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have hp4 : p % 4 = 1 := by
    rw [hp1, Nat.mul_add_mod_self_left]
  have hp2 : p ≠ 2 := by
    intro h
    have hmod : 2 % 4 = 1 := h ▸ hp4
    change (2 : ℕ) = 1 at hmod
    exact (Nat.succ_ne_self 1) hmod
  letI : Fact p.Prime := ⟨hp0⟩
  have hint (x : ℤ) : ¬IsPrimitiveRoot x p := by
    intro hx
    rcases Int.isUnit_iff.mp (hx.isUnit hp0.ne_zero) with rfl | rfl
    · exact hp0.ne_one (hx.unique IsPrimitiveRoot.one)
    · exact hp2 (hx.unique (IsPrimitiveRoot.neg_one 0 (Nat.zero_lt_succ 1).ne))
  letI : NeZero p := ⟨hp0.ne_zero⟩
  have hzmod (x : ZMod p) : ¬IsPrimitiveRoot x p := by
    intro hx
    exact hx.neZero'.out (ZMod.natCast_self p)
  have hleft : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (a.val : ℤ) p :=
    iff_of_false (hzmod a) (hint (a.val : ℤ))
  have hright : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot (-(a.val : ℤ)) p :=
    iff_of_false (hzmod (-a)) (hint (-(a.val : ℤ)))
  rw [hleft, hright]
  exact dummy_assumed hp4 (a.val : ℤ)
