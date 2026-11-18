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
  · rintro ⟨ha, hb, hc, hd⟩
    have ha' : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
    have hb' : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
    have hc' : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
    have habc' : ((a * b * c - 1 : ℕ) : ℤ) = (a : ℤ) * b * c - 1 := by
      have hp : 0 < a * b * c :=
        Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    have hd' : ((a : ℤ) - 1) * ((b : ℤ) - 1) * ((c : ℤ) - 1) ∣
        (a : ℤ) * b * c - 1 := by
      have hcast : (((a - 1) * (b - 1) * (c - 1) : ℕ) : ℤ) ∣
          ((a * b * c - 1 : ℕ) : ℤ) := Int.ofNat_dvd.mpr hd
      push_cast at hcast
      rwa [ha', hb', hc', habc'] at hcast
    have hs := (imo1992_p1_assumed (a : ℤ) (b : ℤ) (c : ℤ) (by omega)
      (by omega) (by omega)).2 hd'
    simp [solution_set] at hs
    omega
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num
