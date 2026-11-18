import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution : ℤ := 231361

def S := { l | ∃ a b m n : ℤ,
    0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < n ∧
    15*a + 16*b = m^2 ∧
    16*a - 15*b = n^2 ∧
    l = min (m^2) (n^2) }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  (∃ (a b : ℕ) (x y : ℕ), 
    0 < a ∧ 0 < b ∧ 0 < x ∧ 0 < y ∧
    15 * a + 16 * b = x^2 ∧ 
    16 * a - 15 * b = y^2 ∧
    min (x^2) (y^2) = 231361) ∧
  (∀ (a b : ℕ) (x y : ℕ), 
    0 < a → 0 < b → 0 < x → 0 < y →
    15 * a + 16 * b = x^2 → 
    16 * a - 15 * b = y^2 →
    min (x^2) (y^2) ≥ 231361) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1996_p4 : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  rcases problem_statement_assumed with ⟨hex, hleast⟩
  constructor
  · rcases hex with ⟨a, b, x, y, ha, hb, hx, hy, hab, hdiff, hmin⟩
    have hy2 : 0 < y^2 := pow_pos hy 2
    have hba : 15 * b ≤ 16 * a := by omega
    refine ⟨(a : ℤ), (b : ℤ), (x : ℤ), (y : ℤ), by exact_mod_cast ha,
      by exact_mod_cast hb, by exact_mod_cast hx, by exact_mod_cast hy,
      by exact_mod_cast hab, by exact_mod_cast hdiff, ?_⟩
    change (231361 : ℤ) = min ((x : ℤ)^2) ((y : ℤ)^2)
    exact_mod_cast hmin.symm
  · intro l hl
    rcases hl with ⟨a, b, x, y, ha, hb, hx, hy, hab, hdiff, rfl⟩
    have ha0 : 0 ≤ a := le_of_lt ha
    have hb0 : 0 ≤ b := le_of_lt hb
    have hx0 : 0 ≤ x := le_of_lt hx
    have hy0 : 0 ≤ y := le_of_lt hy
    have hat : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
    have hbt : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
    have hxt : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
    have hyt : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
    have hbaZ : 15 * b ≤ 16 * a := by nlinarith [sq_nonneg y]
    have hbaZ' : ((15 * b.toNat : ℕ) : ℤ) ≤ ((16 * a.toNat : ℕ) : ℤ) := by
      simpa [hat, hbt] using hbaZ
    have hbaN : 15 * b.toNat ≤ 16 * a.toNat := by exact_mod_cast hbaZ'
    have hn := hleast a.toNat b.toNat x.toNat y.toNat
      (by omega) (by omega) (by omega) (by omega)
      (by
        apply Nat.cast_injective (R := ℤ)
        simpa [hat, hbt, hxt] using hab)
      (by
        apply Nat.cast_injective (R := ℤ)
        simp [Nat.cast_sub hbaN, hat, hbt, hyt, hdiff])
    change (231361 : ℕ) ≤ min (x.toNat^2) (y.toNat^2) at hn
    change (231361 : ℤ) ≤ min (x^2) (y^2)
    have hz : (231361 : ℤ) ≤ ((min (x.toNat^2) (y.toNat^2) : ℕ) : ℤ) := by
      exact_mod_cast hn
    simpa [hxt, hyt] using hz
