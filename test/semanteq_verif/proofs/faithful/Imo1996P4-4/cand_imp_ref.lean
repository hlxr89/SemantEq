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
    a > 0 ∧ b > 0 ∧ 
    x > 0 ∧ y > 0 ∧
    15 * a + 16 * b = x^2 ∧ 
    16 * a - 15 * b = y^2 ∧
    min (x^2) (y^2) = 231361) ∧
  (∀ (a b : ℕ) (x y : ℕ), 
    a > 0 → b > 0 → 
    x > 0 → y > 0 →
    15 * a + 16 * b = x^2 → 
    16 * a - 15 * b = y^2 →
    min (x^2) (y^2) ≥ 231361) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1996_p4 : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  rcases problem_statement_assumed with ⟨hex, hleast⟩
  rcases hex with ⟨a, b, x, y, ha, hb, hx, hy, hab, hsub, hmin⟩
  have horder : 15 * b ≤ 16 * a := by omega
  have habZ : 15 * (a : ℤ) + 16 * (b : ℤ) = (x : ℤ)^2 := by
    exact_mod_cast hab
  have hsubZ : 16 * (a : ℤ) - 15 * (b : ℤ) = (y : ℤ)^2 := by
    have hc := congrArg (fun z : ℕ => (z : ℤ)) hsub
    change ((16 * a - 15 * b : ℕ) : ℤ) = ((y^2 : ℕ) : ℤ) at hc
    rw [Nat.cast_sub horder] at hc
    norm_num at hc ⊢
    exact hc
  refine ⟨?_, ?_⟩
  · refine ⟨a, b, x, y, ?_⟩
    have hminZ := congrArg (fun z : ℕ => (z : ℤ)) hmin.symm
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hb,
      by exact_mod_cast hx, by exact_mod_cast hy, habZ, hsubZ, by simpa [solution] using hminZ⟩
  · intro l hl
    rcases hl with ⟨a', b', x', y', ha', hb', hx', hy', hab', hsub', rfl⟩
    have horder' : 15 * b' ≤ 16 * a' := by nlinarith [sq_nonneg y']
    have haZ : ((a'.toNat : ℕ) : ℤ) = a' := Int.toNat_of_nonneg (le_of_lt ha')
    have hbZ : ((b'.toNat : ℕ) : ℤ) = b' := Int.toNat_of_nonneg (le_of_lt hb')
    have hxZ : ((x'.toNat : ℕ) : ℤ) = x' := Int.toNat_of_nonneg (le_of_lt hx')
    have hyZ : ((y'.toNat : ℕ) : ℤ) = y' := Int.toNat_of_nonneg (le_of_lt hy')
    have habN : 15 * a'.toNat + 16 * b'.toNat = x'.toNat^2 := by
      apply Nat.cast_injective (R := ℤ)
      push_cast
      simpa [haZ, hbZ, hxZ] using hab'
    have hsubN : 16 * a'.toNat - 15 * b'.toNat = y'.toNat^2 := by
      have horderN : 15 * b'.toNat ≤ 16 * a'.toNat := by omega
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub horderN]
      push_cast
      simpa [haZ, hbZ, hyZ] using hsub'
    have hbound := hleast a'.toNat b'.toNat x'.toNat y'.toNat
      (by omega) (by omega) (by omega) (by omega) habN hsubN
    have hboundZ : (231361 : ℤ) ≤ ((min (x'.toNat^2) (y'.toNat^2) : ℕ) : ℤ) := by
      exact_mod_cast hbound
    simpa [solution, hxZ, hyZ] using hboundZ
