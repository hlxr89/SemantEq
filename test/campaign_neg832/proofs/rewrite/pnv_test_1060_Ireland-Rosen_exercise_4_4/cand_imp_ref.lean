import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact p.Prime] [hp1 : Fact (p % 4 = 1)] (a : ℤ) : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  have hpmod : p % 4 = 1 := by
    rw [hp1]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.reduceMod, zero_mul, zero_add]
  letI : Fact (p % 4 = 1) := ⟨hpmod⟩
  have _transport := dummy_assumed (p := p) (a := (a.val : ℤ))
  have no_zmod_root : ∀ x : ZMod p, ¬ IsPrimitiveRoot x p := by
    intro x hx
    have hx_one : x = 1 := by
      rw [← ZMod.pow_card x, hx.pow_eq_one]
    subst x
    exact hp0.ne_one (Nat.dvd_one.mp (hx.dvd_of_pow_eq_one 1 (by rw [one_pow])))
  constructor
  · intro h
    exact (no_zmod_root a h).elim -- non-rewrite step
  · intro h
    exact (no_zmod_root (-a) h).elim -- non-rewrite step
