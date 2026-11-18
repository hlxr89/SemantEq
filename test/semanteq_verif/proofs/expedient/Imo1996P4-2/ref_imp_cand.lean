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
  have ha' : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hb' : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (by omega)
  have hm' : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (by omega)
  have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
  constructor
  · refine ⟨a.toNat, b.toNat, ?_, ?_, m.toNat, n.toNat, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · apply Int.ofNat_inj.mp
      simpa [ha', hb', hm'] using habm
    · have hle : 15 * b ≤ 16 * a := by nlinarith
      have hle' : 15 * b.toNat ≤ 16 * a.toNat := by
        apply Int.ofNat_le.mp
        simpa [ha', hb'] using hle
      apply Int.ofNat_inj.mp
      push_cast [hle']
      simpa [ha', hb', hn'] using habn
    · apply Int.ofNat_inj.mp
      push_cast
      simpa [hm', hn'] using hmin.symm
  · intro a b ha hb
    refine ⟨0, 0, ?_⟩
    omega
