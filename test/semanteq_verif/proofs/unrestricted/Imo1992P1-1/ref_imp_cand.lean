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
    have hdiv' : ((a : ℤ) - 1) * ((b : ℤ) - 1) * ((c : ℤ) - 1) ∣
        (a : ℤ) * (b : ℤ) * (c : ℤ) - 1 := by
      rcases hdiv with ⟨k, hk⟩
      refine ⟨(k : ℤ), ?_⟩
      have hprod : 1 ≤ a * b * c := by
        have : 0 < a * b * c :=
          Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
        omega
      have hk' := congrArg (fun n : ℕ => (n : ℤ)) hk
      simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ a),
        Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_sub (by omega : 1 ≤ c),
        Nat.cast_sub hprod, Nat.cast_one] at hk'
      exact hk'
    have hmem := (imo1992_p1_assumed (a : ℤ) (b : ℤ) (c : ℤ) (by omega)
      (by omega) (by omega)).2 hdiv'
    simp [solution_set] at hmem
    omega
  · rintro (h | h)
    · rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
