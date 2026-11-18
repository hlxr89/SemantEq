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
  lift a to ℕ using le_trans (by simp only [Int.reduceLE]) (le_of_lt ha) with a
  lift b to ℕ using le_trans (by simp only [Int.reduceLE]) (le_of_lt (lt_trans ha hb)) with b
  lift c to ℕ using le_trans (by simp only [Int.reduceLE]) (le_of_lt (lt_trans (lt_trans ha hb) hc)) with c
  have ha' : 1 < a := by exact_mod_cast ha
  have hb' : a < b := by exact_mod_cast hb
  have hc' : b < c := by exact_mod_cast hc
  constructor
  · intro hmem
    have hsol : (a = 2 ∧ b = 4 ∧ c = 8) ∨ (a = 3 ∧ b = 5 ∧ c = 15) := by
      simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      norm_cast at hmem
    have hdiv := ((problem_statement_assumed a b c).2 hsol).2.2.2
    have habc : 1 ≤ a * b * c := by
      simpa only [one_mul] using Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.le_of_lt ha') (Nat.le_of_lt (lt_trans ha' hb')))
        (Nat.le_of_lt (lt_trans (lt_trans ha' hb') hc'))
    have hcast :
        (↑((a - 1) * (b - 1) * (c - 1)) : ℤ) ∣ (↑(a * b * c - 1) : ℤ) :=
      (Int.natCast_dvd_natCast).2 hdiv
    simpa only [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt ha'),
      Nat.cast_sub (Nat.le_of_lt (lt_trans ha' hb')),
      Nat.cast_sub (Nat.le_of_lt (lt_trans (lt_trans ha' hb') hc')),
      Nat.cast_sub habc, Nat.cast_one] using hcast
  · intro hdiv
    have hdiv' : (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by
      have habc : 1 ≤ a * b * c := by
        simpa only [one_mul] using Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.le_of_lt ha') (Nat.le_of_lt (lt_trans ha' hb')))
          (Nat.le_of_lt (lt_trans (lt_trans ha' hb') hc'))
      have hcast :
          (↑((a - 1) * (b - 1) * (c - 1)) : ℤ) ∣ (↑(a * b * c - 1) : ℤ) := by
        simpa only [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt ha'),
          Nat.cast_sub (Nat.le_of_lt (lt_trans ha' hb')),
          Nat.cast_sub (Nat.le_of_lt (lt_trans (lt_trans ha' hb') hc')),
          Nat.cast_sub habc, Nat.cast_one] using hdiv
      exact (Int.natCast_dvd_natCast).1 hcast
    have hsol := (problem_statement_assumed a b c).1 ⟨ha', hb', hc', hdiv'⟩
    simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    norm_cast
