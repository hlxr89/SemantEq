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
theorem dummy {p : ℕ} [hp : Fact p.Prime] (hp1 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have no_root (z : ℤ) : ¬ IsPrimitiveRoot z p := by
    intro h
    rcases Int.isUnit_iff.mp (h.isUnit (by omega)) with rfl | rfl
    · exact h.ne_one (by have := hp.out.two_le; omega) rfl
    · have he := h.eq_orderOf
      norm_num at he
      have := hp.out.two_le
      omega
  exact ⟨fun h ↦ (no_root a h).elim, fun h ↦ (no_root (-a) h).elim⟩
