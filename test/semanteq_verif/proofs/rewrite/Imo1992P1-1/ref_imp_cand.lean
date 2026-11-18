import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set (ℤ × ℤ × ℤ) := {(2, 4, 8), (3, 5, 15)}

-- ===== assumed statement (antecedent) =====
theorem imo1992_p1_assumed (a b c : ℤ) (ha : 1 < a) (hb : a < b) (hc : b < c) :
    ⟨a, b, c⟩ ∈ solution_set ↔
    (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (a b c : ℕ) :
  (1 < a ∧ a < b ∧ b < c ∧ (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1) ↔ 
  (a = 2 ∧ b = 4 ∧ c = 8) ∨ (a = 3 ∧ b = 5 ∧ c = 15) := by
  constructor
  · rintro ⟨ha, hb, hc, hdiv⟩
    have ha' : (1 : ℤ) < (a : ℤ) := by exact_mod_cast ha
    have hb' : (a : ℤ) < (b : ℤ) := by exact_mod_cast hb
    have hc' : (b : ℤ) < (c : ℤ) := by exact_mod_cast hc
    have hdiv' :
        ((a : ℤ) - 1) * ((b : ℤ) - 1) * ((c : ℤ) - 1) ∣
          (a : ℤ) * (b : ℤ) * (c : ℤ) - 1 := by
      have habc : 1 ≤ a * b * c := by
        simpa only [one_mul] using Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.le_of_lt ha) (Nat.le_of_lt (lt_trans ha hb)))
          (Nat.le_of_lt (lt_trans (lt_trans ha hb) hc))
      have hcast :
          (↑((a - 1) * (b - 1) * (c - 1)) : ℤ) ∣ (↑(a * b * c - 1) : ℤ) :=
        (Int.natCast_dvd_natCast).2 hdiv
      simpa only [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt ha),
        Nat.cast_sub (Nat.le_of_lt (lt_trans ha hb)),
        Nat.cast_sub (Nat.le_of_lt (lt_trans (lt_trans ha hb) hc)),
        Nat.cast_sub habc, Nat.cast_one] using hcast
    have hmem := (imo1992_p1_assumed (a : ℤ) (b : ℤ) (c : ℤ) ha' hb' hc').2 hdiv'
    simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    norm_cast at hmem
  · rintro (h | h)
    · rcases h with ⟨rfl, rfl, rfl⟩
      have hmem : (⟨(2 : ℤ), (4 : ℤ), (8 : ℤ)⟩ : ℤ × ℤ × ℤ) ∈ solution_set := by
        simp only [solution_set, Set.mem_insert_iff, true_or]
      have hdiv := (imo1992_p1_assumed 2 4 8 (by simp only [Int.reduceLT])
        (by simp only [Int.reduceLT]) (by simp only [Int.reduceLT])).1 hmem
      refine ⟨by simp only [Nat.reduceLT], by simp only [Nat.reduceLT],
        by simp only [Nat.reduceLT], ?_⟩
      have h2 : 1 ≤ (2 : ℕ) := Nat.le_of_lt (by simp only [Nat.reduceLT])
      have h4 : 1 ≤ (4 : ℕ) := Nat.le_of_lt (by simp only [Nat.reduceLT])
      have h8 : 1 ≤ (8 : ℕ) := Nat.le_of_lt (by simp only [Nat.reduceLT])
      have hp : 1 ≤ (2 : ℕ) * 4 * 8 := by
        simpa only [one_mul] using Nat.mul_le_mul (Nat.mul_le_mul h2 h4) h8
      have hcast :
          (↑((2 - 1) * (4 - 1) * (8 - 1)) : ℤ) ∣ (↑(2 * 4 * 8 - 1) : ℤ) := by
        simpa only [Nat.cast_mul, Nat.cast_sub h2, Nat.cast_sub h4,
          Nat.cast_sub h8, Nat.cast_sub hp, Nat.cast_one] using hdiv
      exact (Int.natCast_dvd_natCast).1 hcast
    · rcases h with ⟨rfl, rfl, rfl⟩
      have hmem : (⟨(3 : ℤ), (5 : ℤ), (15 : ℤ)⟩ : ℤ × ℤ × ℤ) ∈ solution_set := by
        simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
      have hdiv := (imo1992_p1_assumed 3 5 15 (by simp only [Int.reduceLT])
        (by simp only [Int.reduceLT]) (by simp only [Int.reduceLT])).1 hmem
      refine ⟨by simp only [Nat.reduceLT], by simp only [Nat.reduceLT],
        by simp only [Nat.reduceLT], ?_⟩
      have h3 : 1 ≤ (3 : ℕ) := Nat.le_of_lt (by simp only [Nat.reduceLT])
      have h5 : 1 ≤ (5 : ℕ) := Nat.le_of_lt (by simp only [Nat.reduceLT])
      have h15 : 1 ≤ (15 : ℕ) := Nat.le_of_lt (by simp only [Nat.reduceLT])
      have hp : 1 ≤ (3 : ℕ) * 5 * 15 := by
        simpa only [one_mul] using Nat.mul_le_mul (Nat.mul_le_mul h3 h5) h15
      have hcast :
          (↑((3 - 1) * (5 - 1) * (15 - 1)) : ℤ) ∣ (↑(3 * 5 * 15 - 1) : ℤ) := by
        simpa only [Nat.cast_mul, Nat.cast_sub h3, Nat.cast_sub h5,
          Nat.cast_sub h15, Nat.cast_sub hp, Nat.cast_one] using hdiv
      exact (Int.natCast_dvd_natCast).1 hcast
