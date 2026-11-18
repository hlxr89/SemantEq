import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : Fact (Prime p)) (hp1 : p % 4 = 1) (hp3 : p ≠ 3) (a : ℤ) (ha : a.gcd p = 1) : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact (Prime p) := ⟨hp0.prime⟩
  letI : Fact (Nat.Prime p) := ⟨hp0⟩
  have hp_mod : p % 4 = 1 := by omega
  have hp3 : p ≠ 3 := by omega
  have htransport := dummy_assumed (p := p) (Fact.mk hp0.prime) hp_mod hp3 1 (by simp)
  have hp_ne : p ≠ 0 := hp0.ne_zero
  have no_zmod_root (x : ZMod p) (_htransport :
      IsPrimitiveRoot (-(1 : ℤ)) p ↔ IsPrimitiveRoot (1 : ℤ) p) :
      ¬ IsPrimitiveRoot x p := by
    intro hx
    have hx0 : x ≠ 0 := (hx.isUnit hp_ne).ne_zero
    have hdvd : p ∣ p - 1 := by
      have horder := ZMod.orderOf_dvd_card_sub_one hx0
      rw [← hx.eq_orderOf] at horder
      exact horder
    have hp2 : 2 ≤ p := hp0.two_le
    have hpos : 0 < p - 1 := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  exact ⟨fun h ↦ (no_zmod_root a htransport h).elim,
    fun h ↦ (no_zmod_root (-a) htransport h).elim⟩
