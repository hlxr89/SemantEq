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
  (∃ (a b x y : ℕ), 
    0 < a ∧ 0 < b ∧ 
    0 < x ∧ 0 < y ∧
    15 * a + 16 * b = x^2 ∧ 
    16 * a - 15 * b = y^2 ∧
    min (x^2) (y^2) = 231361) ∧
  (∀ (a b x y : ℕ), 
    0 < a ∧ 0 < b ∧ 
    0 < x ∧ 0 < y ∧
    15 * a + 16 * b = x^2 ∧ 
    16 * a - 15 * b = y^2 →
    min (x^2) (y^2) ≥ 231361) := by
  rcases imo1996_p4_assumed with ⟨hex, hmin⟩
  constructor
  · rcases hex with ⟨a, b, x, y, ha, hb, hx, hy, habx, haby, hsol⟩
    have ha0 : 0 ≤ a := le_of_lt ha
    have hb0 : 0 ≤ b := le_of_lt hb
    have hx0 : 0 ≤ x := le_of_lt hx
    have hy0 : 0 ≤ y := le_of_lt hy
    refine ⟨a.toNat, b.toNat, x.toNat, y.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · apply Int.ofNat_inj.mp
      push_cast
      simpa [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0,
        Int.toNat_of_nonneg hx0] using habx
    · have hba : 15 * b ≤ 16 * a := by nlinarith [sq_nonneg y]
      have hbaCast : ((15 * b.toNat : ℕ) : ℤ) ≤ ((16 * a.toNat : ℕ) : ℤ) := by
        push_cast
        simpa [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] using hba
      have hbaNat : 15 * b.toNat ≤ 16 * a.toNat := by exact_mod_cast hbaCast
      apply Int.ofNat_inj.mp
      rw [Nat.cast_sub hbaNat]
      push_cast
      simpa [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0,
        Int.toNat_of_nonneg hy0] using haby
    · apply Int.ofNat_inj.mp
      rw [Nat.cast_min]
      push_cast
      simpa [solution, Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0] using hsol.symm
  · intro a b x y h
    rcases h with ⟨ha, hb, hx, hy, habx, haby⟩
    have hsubpos : 0 < 16 * a - 15 * b := by rw [haby]; positivity
    have hba : 15 * b ≤ 16 * a := by omega
    have hz := hmin (min ((x : ℤ)^2) ((y : ℤ)^2))
    have hzmem : min ((x : ℤ)^2) ((y : ℤ)^2) ∈ S := by
      refine ⟨(a : ℤ), (b : ℤ), (x : ℤ), (y : ℤ), ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · exact_mod_cast ha
      · exact_mod_cast hb
      · exact_mod_cast hx
      · exact_mod_cast hy
      · exact_mod_cast habx
      · have hcast : ((16 * a - 15 * b : ℕ) : ℤ) = ((y^2 : ℕ) : ℤ) := by
          exact_mod_cast haby
        rw [Nat.cast_sub hba] at hcast
        simpa using hcast
    have hz' := hz hzmem
    have hcast : (231361 : ℤ) ≤ ((min (x^2) (y^2) : ℕ) : ℤ) := by
      rw [Nat.cast_min]
      push_cast
      simpa [solution] using hz'
    exact_mod_cast hcast
