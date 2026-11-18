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
  (∃ (a b : ℕ), a > 0 ∧ b > 0 ∧ 
   ∃ (x y : ℕ), x > 0 ∧ y > 0 ∧ 
   15 * a + 16 * b = x^2 ∧ 
   16 * a - 15 * b = y^2 ∧
   min (x^2) (y^2) = 231361) ∧
  (∀ (a b : ℕ), a > 0 → b > 0 → 
   ∃ (x y : ℕ), x > 0 ∧ y > 0 ∧ 
   15 * a + 16 * b = x^2 ∧ 
   16 * a - 15 * b = y^2 →
   min (x^2) (y^2) ≥ 231361) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1996_p4 : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  rcases problem_statement_assumed with ⟨hex, hbound⟩
  constructor
  · rcases hex with ⟨a, b, ha, hb, x, y, hx, hy, habx, haby, hmin⟩
    have hab_nonneg : 15 * b ≤ 16 * a := by
      apply Nat.le_of_lt
      rw [← Nat.sub_pos_iff_lt, haby]
      exact pow_pos hy 2
    change (231361 : ℤ) ∈ S
    refine ⟨a, b, x, y, ?_⟩
    refine ⟨by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hx,
      by exact_mod_cast hy, by exact_mod_cast habx, ?_, ?_⟩
    · have haby_cast := congrArg (fun z : ℕ => (z : ℤ)) haby
      simpa only [Int.ofNat_sub hab_nonneg, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_pow] using haby_cast
    · have hmin_cast := congrArg (fun z : ℕ => (z : ℤ)) hmin
      symm
      simpa only [Nat.cast_min, Nat.cast_pow, Nat.cast_ofNat] using hmin_cast
  · -- not proved: the candidate existentially selects x and y before its implication, so it cannot bound a supplied solution
    sorry
