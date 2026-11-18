import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (h : p.Prime) (hp : ∃ t : ℕ, p = 4 * t + 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  letI : NeZero p := ⟨hp0.ne_zero⟩
  have htransport := dummy_assumed hp0 ⟨t, hp1⟩ (a.val : ℤ)
  constructor
  · intro ha
    have hc : NeZero ((p : ℕ) : ZMod p) := ha.neZero'
    exact (fun _ => (hc.out (ZMod.natCast_self p)).elim) htransport -- non-rewrite step
  · intro ha
    have hc : NeZero ((p : ℕ) : ZMod p) := ha.neZero'
    exact (fun _ => (hc.out (ZMod.natCast_self p)).elim) htransport -- non-rewrite step
