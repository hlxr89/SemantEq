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
  rcases imo1996_p4_assumed with ⟨hsol, hleast⟩
  rcases hsol with ⟨a, b, x, y, ha, hb, hx, hy, hab, hsub, hmin⟩
  have horder : 15 * b ≤ 16 * a := by nlinarith [sq_nonneg y]
  refine ⟨?_, ?_⟩
  · refine ⟨a.toNat, b.toNat, x.toNat, y.toNat, ?_⟩
    have ha' : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (le_of_lt ha)
    have hb' : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb)
    have hx' : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (le_of_lt hx)
    have hy' : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (le_of_lt hy)
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · apply Nat.cast_injective (R := ℤ)
      push_cast
      simpa [ha', hb', hx'] using hab
    constructor
    · have horderN : 15 * b.toNat ≤ 16 * a.toNat := by omega
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub horderN]
      push_cast
      simpa [ha', hb', hy'] using hsub
    · apply Nat.cast_injective (R := ℤ)
      push_cast
      simpa [hx', hy', solution] using hmin.symm
  · intro a' b' x' y' ha' hb' hx' hy' hab' hsub'
    have hy2' : 0 < y'^2 := pow_pos hy' 2
    have horder' : 15 * b' ≤ 16 * a' := by omega
    have habZ : 15 * (a' : ℤ) + 16 * (b' : ℤ) = (x' : ℤ)^2 := by
      exact_mod_cast hab'
    have hsubZ : 16 * (a' : ℤ) - 15 * (b' : ℤ) = (y' : ℤ)^2 := by
      have hc := congrArg (fun z : ℕ => (z : ℤ)) hsub'
      change ((16 * a' - 15 * b' : ℕ) : ℤ) = ((y'^2 : ℕ) : ℤ) at hc
      rw [Nat.cast_sub horder'] at hc
      norm_num at hc ⊢
      exact hc
    have hmem : ((min (x'^2) (y'^2) : ℕ) : ℤ) ∈ S := by
      refine ⟨a', b', x', y', ?_⟩
      exact ⟨by exact_mod_cast ha', by exact_mod_cast hb',
        by exact_mod_cast hx', by exact_mod_cast hy', habZ, hsubZ, by norm_num⟩
    have hbnd := hleast _ hmem
    change (231361 : ℤ) ≤ ((min (x'^2) (y'^2) : ℕ) : ℤ) at hbnd
    exact_mod_cast hbnd
