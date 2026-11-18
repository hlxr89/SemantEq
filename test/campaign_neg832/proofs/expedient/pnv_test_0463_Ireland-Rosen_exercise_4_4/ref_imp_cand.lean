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
  have hn : ∀ x : ℤ, ¬IsPrimitiveRoot x p := by
    intro x h
    have hp0 : p ≠ 0 := by omega
    rcases Int.isUnit_iff.mp (h.isUnit hp0) with rfl | rfl
    · exact h.ne_one hp.out.one_lt rfl
    · have heq : p = 2 := h.unique (IsPrimitiveRoot.neg_one 0 (by norm_num))
      subst p
      norm_num at hp4
  exact ⟨fun h ↦ (hn a h).elim, fun h ↦ (hn (-a) h).elim⟩
