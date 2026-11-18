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
  let A := a.toNat
  let B := b.toNat
  let C := c.toNat
  have ha0 : 0 ≤ a := by omega
  have hb0 : 0 ≤ b := by omega
  have hc0 : 0 ≤ c := by omega
  have hA : (A : ℤ) = a := by simpa [A] using Int.toNat_of_nonneg ha0
  have hB : (B : ℤ) = b := by simpa [B] using Int.toNat_of_nonneg hb0
  have hC : (C : ℤ) = c := by simpa [C] using Int.toNat_of_nonneg hc0
  have hAn : 1 < A := by exact_mod_cast hA ▸ ha
  have hAB : A < B := by exact_mod_cast hA ▸ hB ▸ hb
  have hBC : B < C := by exact_mod_cast hB ▸ hC ▸ hc
  have hsA : ((A - 1 : ℕ) : ℤ) = (A : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hsB : ((B - 1 : ℕ) : ℤ) = (B : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hsC : ((C - 1 : ℕ) : ℤ) = (C : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hsP : (((A * B * C - 1 : ℕ) : ℤ)) = (A : ℤ) * B * C - 1 := by
    have hp : 0 < A * B * C := by
      exact mul_pos (mul_pos (by omega) (by omega)) (by omega)
    rw [Nat.cast_sub (by omega)]
    norm_num
  constructor
  · intro hmem
    have hintsol : ((A : ℤ) = 2 ∧ (B : ℤ) = 4 ∧ (C : ℤ) = 8) ∨
        ((A : ℤ) = 3 ∧ (B : ℤ) = 5 ∧ (C : ℤ) = 15) := by
      simpa [solution_set, hA, hB, hC] using hmem
    have hsol : (A = 2 ∧ B = 4 ∧ C = 8) ∨ (A = 3 ∧ B = 5 ∧ C = 15) := by
      exact_mod_cast hintsol
    have hdvdN : (A - 1) * (B - 1) * (C - 1) ∣ A * B * C - 1 :=
      (problem_statement_assumed A B C).2 hsol |>.2.2.2
    have hdvdZ : ((A : ℤ) - 1) * ((B : ℤ) - 1) * ((C : ℤ) - 1) ∣
        (A : ℤ) * B * C - 1 := by
      rw [← hsA, ← hsB, ← hsC, ← hsP]
      exact_mod_cast hdvdN
    simpa [hA, hB, hC] using hdvdZ
  · intro hdvd
    have hdvdN : (A - 1) * (B - 1) * (C - 1) ∣ A * B * C - 1 := by
      have hdvdZ : ((A : ℤ) - 1) * ((B : ℤ) - 1) * ((C : ℤ) - 1) ∣
          (A : ℤ) * B * C - 1 := by
        simpa [hA, hB, hC] using hdvd
      have hcast : (((A - 1) * (B - 1) * (C - 1) : ℕ) : ℤ) ∣
          ((A * B * C - 1 : ℕ) : ℤ) := by
        simpa only [Nat.cast_mul, hsA, hsB, hsC, hsP] using hdvdZ
      exact_mod_cast hcast
    have hsol : (A = 2 ∧ B = 4 ∧ C = 8) ∨ (A = 3 ∧ B = 5 ∧ C = 15) :=
      (problem_statement_assumed A B C).1 ⟨hAn, hAB, hBC, hdvdN⟩
    have hintsol : ((A : ℤ) = 2 ∧ (B : ℤ) = 4 ∧ (C : ℤ) = 8) ∨
        ((A : ℤ) = 3 ∧ (B : ℤ) = 5 ∧ (C : ℤ) = 15) := by
      exact_mod_cast hsol
    simpa [solution_set, hA, hB, hC] using hintsol
