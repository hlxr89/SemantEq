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
  · rintro ⟨ha, hb, hc, hdvd⟩
    have ha' : (1 : ℤ) < a := by exact_mod_cast ha
    have hb' : (a : ℤ) < b := by exact_mod_cast hb
    have hc' : (b : ℤ) < c := by exact_mod_cast hc
    have hsa : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hsb : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hsc : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hsp : (((a * b * c - 1 : ℕ) : ℤ)) = (a : ℤ) * b * c - 1 := by
      have hp : 0 < a * b * c := by
        exact mul_pos (mul_pos (by omega) (by omega)) (by omega)
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hdvd' : ((a : ℤ) - 1) * ((b : ℤ) - 1) * ((c : ℤ) - 1) ∣
        (a : ℤ) * b * c - 1 := by
      rw [← hsa, ← hsb, ← hsc, ← hsp]
      exact_mod_cast hdvd
    have hmem : (⟨(a : ℤ), (b : ℤ), (c : ℤ)⟩ : ℤ × ℤ × ℤ) ∈ solution_set :=
      (imo1992_p1_assumed (a : ℤ) (b : ℤ) (c : ℤ) ha' hb' hc').2 hdvd'
    have hintsol : ((a : ℤ) = 2 ∧ (b : ℤ) = 4 ∧ (c : ℤ) = 8) ∨
        ((a : ℤ) = 3 ∧ (b : ℤ) = 5 ∧ (c : ℤ) = 15) := by
      simpa [solution_set] using hmem
    exact_mod_cast hintsol
  · intro hsol
    have ha : 1 < a := by rcases hsol with h | h <;> omega
    have hb : a < b := by rcases hsol with h | h <;> omega
    have hc : b < c := by rcases hsol with h | h <;> omega
    have ha' : (1 : ℤ) < a := by exact_mod_cast ha
    have hb' : (a : ℤ) < b := by exact_mod_cast hb
    have hc' : (b : ℤ) < c := by exact_mod_cast hc
    have hsa : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hsb : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hsc : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hsp : (((a * b * c - 1 : ℕ) : ℤ)) = (a : ℤ) * b * c - 1 := by
      have hp : 0 < a * b * c := by
        exact mul_pos (mul_pos (by omega) (by omega)) (by omega)
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hmem : (⟨(a : ℤ), (b : ℤ), (c : ℤ)⟩ : ℤ × ℤ × ℤ) ∈ solution_set := by
      have hintsol : ((a : ℤ) = 2 ∧ (b : ℤ) = 4 ∧ (c : ℤ) = 8) ∨
          ((a : ℤ) = 3 ∧ (b : ℤ) = 5 ∧ (c : ℤ) = 15) := by
        exact_mod_cast hsol
      simpa [solution_set] using hintsol
    have hdvd' : ((a : ℤ) - 1) * ((b : ℤ) - 1) * ((c : ℤ) - 1) ∣
        (a : ℤ) * b * c - 1 :=
      (imo1992_p1_assumed (a : ℤ) (b : ℤ) (c : ℤ) ha' hb' hc').1 hmem
    have hdvd : (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by
      have hcast : (((a - 1) * (b - 1) * (c - 1) : ℕ) : ℤ) ∣
          ((a * b * c - 1 : ℕ) : ℤ) := by
        simpa only [Nat.cast_mul, hsa, hsb, hsc, hsp] using hdvd'
      exact_mod_cast hcast
    exact ⟨ha, hb, hc, hdvd⟩
