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
  rcases imo1996_p4_assumed.1 with
    ⟨a, b, m, n, ha, hb, hm, hn, habm, habn, hmin⟩
  constructor
  · refine ⟨a.toNat, b.toNat, ?_, ?_, m.toNat, n.toNat, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · apply Nat.cast_injective (R := ℤ)
      push_cast
      simpa [Int.toNat_of_nonneg (by omega : 0 ≤ a),
        Int.toNat_of_nonneg (by omega : 0 ≤ b),
        Int.toNat_of_nonneg (by omega : 0 ≤ m)] using habm
    · have hle : 15 * b ≤ 16 * a := by nlinarith [sq_nonneg n]
      have hle' : 15 * b.toNat ≤ 16 * a.toNat := by
        exact_mod_cast (show (15 * b.toNat : ℤ) ≤ 16 * a.toNat by
          push_cast
          simpa [Int.toNat_of_nonneg (by omega : 0 ≤ a),
            Int.toNat_of_nonneg (by omega : 0 ≤ b)] using hle)
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hle']
      push_cast
      simpa [Int.toNat_of_nonneg (by omega : 0 ≤ a),
        Int.toNat_of_nonneg (by omega : 0 ≤ b),
        Int.toNat_of_nonneg (by omega : 0 ≤ n)] using habn
    · apply Nat.cast_injective (R := ℤ)
      push_cast
      simpa [Int.toNat_of_nonneg (by omega : 0 ≤ m),
        Int.toNat_of_nonneg (by omega : 0 ≤ n)] using hmin.symm
  · intro a b ha hb
    refine ⟨1, 1, ?_⟩
    rintro ⟨-, -, hab, -⟩
    omega
