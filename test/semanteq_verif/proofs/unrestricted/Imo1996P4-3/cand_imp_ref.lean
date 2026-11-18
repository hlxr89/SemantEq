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
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1996_p4 : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  rcases problem_statement_assumed with ⟨hex, hmin⟩
  constructor
  · rcases hex with ⟨a, b, x, y, ha, hb, hx, hy, habx, haby, hxy⟩
    refine ⟨(a : ℤ), (b : ℤ), (x : ℤ), (y : ℤ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast ha
    · exact_mod_cast hb
    · exact_mod_cast hx
    · exact_mod_cast hy
    · exact_mod_cast habx
    · have hsubpos : 0 < 16 * a - 15 * b := by rw [haby]; positivity
      have hba : 15 * b ≤ 16 * a := by omega
      have hcast : ((16 * a - 15 * b : ℕ) : ℤ) = ((y^2 : ℕ) : ℤ) := by
        exact_mod_cast haby
      rw [Nat.cast_sub hba] at hcast
      simpa using hcast
    · calc
        solution = (231361 : ℤ) := rfl
        _ = ((min (x^2) (y^2) : ℕ) : ℤ) := by exact_mod_cast hxy.symm
        _ = min ((x : ℤ)^2) ((y : ℤ)^2) := by rw [Nat.cast_min]; push_cast; rfl
  · intro l hl
    rcases hl with ⟨a, b, x, y, ha, hb, hx, hy, habx, haby, rfl⟩
    have ha0 : 0 ≤ a := le_of_lt ha
    have hb0 : 0 ≤ b := le_of_lt hb
    have hx0 : 0 ≤ x := le_of_lt hx
    have hy0 : 0 ≤ y := le_of_lt hy
    have hba : 15 * b ≤ 16 * a := by nlinarith [sq_nonneg y]
    have hn := hmin a.toNat b.toNat x.toNat y.toNat
    have hnat : min (x.toNat^2) (y.toNat^2) ≥ 231361 := by
      apply hn
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · omega
      · apply Int.ofNat_inj.mp
        push_cast
        simpa [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0,
          Int.toNat_of_nonneg hx0] using habx
      · have hbaCast : ((15 * b.toNat : ℕ) : ℤ) ≤ ((16 * a.toNat : ℕ) : ℤ) := by
          push_cast
          simpa [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] using hba
        have hbaNat : 15 * b.toNat ≤ 16 * a.toNat := by exact_mod_cast hbaCast
        apply Int.ofNat_inj.mp
        rw [Nat.cast_sub hbaNat]
        push_cast
        simpa [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0,
          Int.toNat_of_nonneg hy0] using haby
    have hcast : (231361 : ℤ) ≤ ((min (x.toNat^2) (y.toNat^2) : ℕ) : ℤ) := by
      exact_mod_cast hnat
    rw [Nat.cast_min] at hcast
    push_cast at hcast
    simpa [solution, Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0] using hcast
