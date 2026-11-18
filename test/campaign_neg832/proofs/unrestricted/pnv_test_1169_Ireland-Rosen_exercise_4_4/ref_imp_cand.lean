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
  have hpgt : 1 < p := hp.out.one_lt
  have hp0 : p ≠ 0 := by omega
  have no_root : ∀ x : ℤ, ¬ IsPrimitiveRoot x p := by
    intro x hx
    rcases (pow_eq_one_iff_of_ne_zero hp0).mp hx.pow_eq_one with rfl | ⟨rfl, heven⟩
    · exact hx.ne_one hpgt rfl
    · obtain ⟨k, hk⟩ := heven
      omega
  exact ⟨fun ha ↦ (no_root a ha).elim, fun hna ↦ (no_root (-a) hna).elim⟩
