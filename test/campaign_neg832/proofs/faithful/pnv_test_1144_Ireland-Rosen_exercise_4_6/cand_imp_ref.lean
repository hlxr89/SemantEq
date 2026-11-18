import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : ∃ n : ℕ, p = 2^n + 1 ∧ Nat.Prime p) : IsPrimitiveRoot 3 p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6 {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  have h := dummy_assumed ⟨n, hpn, hp⟩
  have hp_zero : p = 0 := by
    have hpow := h.pow_eq_one
    simpa using hpow
  rw [hp_zero] at h ⊢
  exact h.map_of_injective (f := Nat.castRingHom (ZMod 0)) Nat.cast_injective
