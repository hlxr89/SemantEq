import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution : ℤ := 231361

def S := { l | ∃ a b m n : ℤ,
    0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < n ∧
    15*a + 16*b = m^2 ∧
    16*a - 15*b = n^2 ∧
    l = min (m^2) (n^2) }

-- ===== assumed statement (antecedent) =====
theorem imo1996_p4_assumed : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
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
  rcases imo1996_p4_assumed with ⟨⟨a, b, x, y, ha, hb, hx, hy, habx, haby, hmin⟩, hleast⟩
  have ha_cast : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (le_of_lt ha)
  have hb_cast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb)
  have hx_cast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (le_of_lt hx)
  have hy_cast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (le_of_lt hy)
  constructor
  · refine ⟨a.toNat, b.toNat, x.toNat, y.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : (0 : ℤ) < (a.toNat : ℤ) := by rw [ha_cast]; exact ha
      exact_mod_cast this
    · have : (0 : ℤ) < (b.toNat : ℤ) := by rw [hb_cast]; exact hb
      exact_mod_cast this
    · have : (0 : ℤ) < (x.toNat : ℤ) := by rw [hx_cast]; exact hx
      exact_mod_cast this
    · have : (0 : ℤ) < (y.toNat : ℤ) := by rw [hy_cast]; exact hy
      exact_mod_cast this
    · rw [← ha_cast, ← hb_cast, ← hx_cast] at habx
      exact_mod_cast habx
    · have hsubZ : 15 * b ≤ 16 * a := by
        rw [← sub_nonneg]
        rw [haby]
        exact sq_nonneg y
      have hsub : 15 * b.toNat ≤ 16 * a.toNat := by
        rw [← ha_cast, ← hb_cast] at hsubZ
        exact_mod_cast hsubZ
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hsub]
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, ha_cast, hb_cast, hy_cast] using haby
    · apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_min]
      simpa only [Nat.cast_pow, Nat.cast_ofNat, hx_cast, hy_cast, solution] using hmin.symm
  · intro a' b' x' y' ha' hb' hx' hy' habx' haby'
    have hsub : 15 * b' ≤ 16 * a' := by
      exact Nat.le_of_lt (Nat.sub_ne_zero_iff_lt.mp (by
        rw [haby']
        exact pow_ne_zero 2 (Nat.ne_of_gt hy')))
    have hmem : (↑(min (x'^2) (y'^2) : ℕ) : ℤ) ∈ S := by
      refine ⟨a', b', x', y', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact_mod_cast ha'
      · exact_mod_cast hb'
      · exact_mod_cast hx'
      · exact_mod_cast hy'
      · exact_mod_cast habx'
      · have hc := congrArg (fun n : ℕ => (n : ℤ)) haby'
        change (↑(16 * a' - 15 * b') : ℤ) = ↑(y' ^ 2) at hc
        rw [Nat.cast_sub hsub] at hc
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hc
      · norm_cast
    have h := hleast (↑(min (x'^2) (y'^2) : ℕ) : ℤ) hmem
    change (231361 : ℤ) ≤ ↑(min (x'^2) (y'^2) : ℕ) at h
    exact_mod_cast h
