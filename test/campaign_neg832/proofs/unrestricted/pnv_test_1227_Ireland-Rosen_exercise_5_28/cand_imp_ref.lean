import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : p ≡ 1 [MOD 4]) : (∃ x : ℤ, x^4 ≡ 2 [ZMOD p]) ↔ (∃ A B : ℤ, p = A^2 + 64 * B^2) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_28 {p : ℕ} (hp : p.Prime) (hp1 : p ≡ 1 [MOD 4]):
  (∃ x, x^4 ≡ 2 [MOD p]) ↔ ∃ A B, p = A^2 + 64*B^2 := by
  have h := dummy_assumed (p := p) hp1
  constructor
  · rintro ⟨x, hx⟩
    have hxz : ∃ x : ℤ, x^4 ≡ 2 [ZMOD p] := by
      exact ⟨x, by exact_mod_cast hx⟩
    rcases h.mp hxz with ⟨A, B, hAB⟩
    refine ⟨A.natAbs, B.natAbs, ?_⟩
    have hAB' : (p : ℤ) = |A|^2 + 64 * |B|^2 := by
      simpa only [sq_abs] using hAB
    have hcast : (p : ℤ) = ((A.natAbs^2 + 64 * B.natAbs^2 : ℕ) : ℤ) := by
      push_cast
      simpa only [Int.natCast_natAbs] using hAB'
    exact_mod_cast hcast
  · rintro ⟨A, B, hAB⟩
    have hABz : ∃ A B : ℤ, p = A^2 + 64 * B^2 := by
      exact ⟨A, B, by exact_mod_cast hAB⟩
    rcases h.mpr hABz with ⟨x, hx⟩
    refine ⟨x.natAbs, ?_⟩
    have hx' : |x|^4 ≡ 2 [ZMOD p] := by
      have hxpow : |x|^4 = x^4 := by
        calc
          |x|^4 = (|x|^2)^2 := by ring
          _ = (x^2)^2 := by rw [sq_abs]
          _ = x^4 := by ring
      rwa [hxpow]
    have hxcast : (((x.natAbs)^4 : ℕ) : ℤ) ≡ 2 [ZMOD p] := by
      push_cast
      simpa only [Int.natCast_natAbs] using hx'
    exact_mod_cast hxcast
