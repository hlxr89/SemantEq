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
  have ha0 : 0 ≤ a := by omega
  have hb0 : 0 ≤ b := by omega
  have hc0 : 0 ≤ c := by omega
  let A := a.toNat
  let B := b.toNat
  let C := c.toNat
  have hA : (A : ℤ) = a := by simp [A, Int.toNat_of_nonneg ha0]
  have hB : (B : ℤ) = b := by simp [B, Int.toNat_of_nonneg hb0]
  have hC : (C : ℤ) = c := by simp [C, Int.toNat_of_nonneg hc0]
  have horder : 1 < A ∧ A < B ∧ B < C := by
    omega
  constructor
  · intro hmem
    simp [solution_set] at hmem
    rcases hmem with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
  · intro hdiv
    have hdivNat : (A - 1) * (B - 1) * (C - 1) ∣ A * B * C - 1 := by
      rcases hdiv with ⟨k, hk⟩
      have hfactorpos : 0 < (a - 1) * (b - 1) * (c - 1) :=
        mul_pos (mul_pos (by omega) (by omega)) (by omega)
      have habcpos : 0 < a * b * c :=
        mul_pos (mul_pos (by omega) (by omega)) (by omega)
      have hk0 : 0 ≤ k := by
        by_contra hn
        have hprodneg : (a - 1) * (b - 1) * (c - 1) * k < 0 :=
          mul_neg_of_pos_of_neg hfactorpos (by omega)
        omega
      have hK : ((k.toNat : ℕ) : ℤ) = k := by
        simp [Int.toNat_of_nonneg hk0]
      have hleft : (((A - 1) * (B - 1) * (C - 1) : ℕ) : ℤ) =
          (a - 1) * (b - 1) * (c - 1) := by
        simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ A),
          Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_sub (by omega : 1 ≤ C),
          Nat.cast_one]
        rw [hA, hB, hC]
      have hprod : 1 ≤ A * B * C := by
        have : 0 < A * B * C :=
          Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
        omega
      have hright : ((A * B * C - 1 : ℕ) : ℤ) = a * b * c - 1 := by
        simp only [Nat.cast_sub hprod, Nat.cast_mul, Nat.cast_one]
        rw [hA, hB, hC]
      refine ⟨k.toNat, ?_⟩
      apply Int.ofNat_inj.mp
      rw [Nat.cast_mul, hleft, hright, hK]
      exact hk
    have hclass := (problem_statement_assumed A B C).1
      ⟨horder.1, horder.2.1, horder.2.2, hdivNat⟩
    rcases hclass with h | h
    · rcases h with ⟨hA2, hB4, hC8⟩
      have : a = 2 ∧ b = 4 ∧ c = 8 := by omega
      simp [solution_set]
      exact Or.inl this
    · rcases h with ⟨hA3, hB5, hC15⟩
      have : a = 3 ∧ b = 5 ∧ c = 15 := by omega
      simp [solution_set]
      exact Or.inr this
