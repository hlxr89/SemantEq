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
theorem dummy {p : ℕ} (h : p.Prime) (hp : ∃ t : ℕ, p = 4 * t + 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  obtain ⟨t, rfl⟩ := hp
  have hn : 4 * t + 1 ≠ 0 := Nat.succ_ne_zero _
  have hneven : ¬ Even (4 * t + 1) := by
    rintro ⟨k, hk⟩
    omega
  have htransport := exercise_4_4_assumed h rfl (a : ZMod (4 * t + 1))
  constructor
  · intro ha
    have ha1 : a = 1 :=
      (pow_eq_one_iff_of_ne_zero hn).mp ha.pow_eq_one |>.resolve_right fun ha' => hneven ha'.2
    exact (fun _ => (ha.ne_one h.one_lt ha1).elim) htransport -- non-rewrite step
  · intro ha
    have ha1 : -a = 1 :=
      (pow_eq_one_iff_of_ne_zero hn).mp ha.pow_eq_one |>.resolve_right fun ha' => hneven ha'.2
    exact (fun _ => (ha.ne_one h.one_lt ha1).elim) htransport -- non-rewrite step
