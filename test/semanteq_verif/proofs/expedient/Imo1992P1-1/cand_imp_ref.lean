import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set (ℤ × ℤ × ℤ) := {(2, 4, 8), (3, 5, 15)}

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a b c : ℕ) :
  (1 < a ∧ a < b ∧ b < c ∧ (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1) ↔ 
  (a = 2 ∧ b = 4 ∧ c = 8) ∨ (a = 3 ∧ b = 5 ∧ c = 15) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1992_p1 (a b c : ℤ) (ha : 1 < a) (hb : a < b) (hc : b < c) :
    ⟨a, b, c⟩ ∈ solution_set ↔
    (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by
  constructor
  · intro hs
    simp [solution_set] at hs
    rcases hs with h | h <;> rcases h with ⟨rfl, rfl, rfl⟩ <;> norm_num
  · intro hd
    have ha' : ((a.toNat - 1 : ℕ) : ℤ) = a - 1 := by omega
    have hb' : ((b.toNat - 1 : ℕ) : ℤ) = b - 1 := by omega
    have hc' : ((c.toNat - 1 : ℕ) : ℤ) = c - 1 := by omega
    have hapos : 0 ≤ a := by omega
    have hbpos : 0 ≤ b := by omega
    have hcpos : 0 ≤ c := by omega
    have hapos' : 0 < a.toNat := by omega
    have hbpos' : 0 < b.toNat := by omega
    have hcpos' : 0 < c.toNat := by omega
    have habc' : ((a.toNat * b.toNat * c.toNat - 1 : ℕ) : ℤ) =
        a * b * c - 1 := by
      have hp : 0 < a.toNat * b.toNat * c.toNat := by positivity
      rw [Nat.cast_sub (by omega)]
      push_cast
      simp [Int.toNat_of_nonneg hapos, Int.toNat_of_nonneg hbpos,
        Int.toNat_of_nonneg hcpos]
    have hD : (((a.toNat - 1) * (b.toNat - 1) * (c.toNat - 1) : ℕ) : ℤ) =
        (a - 1) * (b - 1) * (c - 1) := by
      push_cast
      rw [ha', hb', hc']
    have hN : ((a.toNat * b.toNat * c.toNat - 1 : ℕ) : ℤ) =
        a * b * c - 1 := habc'
    have hd' : (a.toNat - 1) * (b.toNat - 1) * (c.toNat - 1) ∣
        a.toNat * b.toNat * c.toNat - 1 := by
      apply Int.ofNat_dvd.mp
      rwa [hD, hN]
    have hclass := (problem_statement_assumed a.toNat b.toNat c.toNat).1
      (show 1 < a.toNat ∧ a.toNat < b.toNat ∧ b.toNat < c.toNat ∧
          (a.toNat - 1) * (b.toNat - 1) * (c.toNat - 1) ∣
            a.toNat * b.toNat * c.toNat - 1 by
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        · exact hd')
    simp [solution_set]
    omega
