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
  (∃ (a b x y : ℕ), 
    0 < a ∧ 0 < b ∧ 
    0 < x ∧ 0 < y ∧
    15 * a + 16 * b = x^2 ∧ 
    16 * a - 15 * b = y^2 ∧
    min (x^2) (y^2) = 231361) ∧
  (∀ (a b x y : ℕ), 
    0 < a ∧ 0 < b ∧ 
    0 < x ∧ 0 < y ∧
    15 * a + 16 * b = x^2 ∧ 
    16 * a - 15 * b = y^2 →
    min (x^2) (y^2) ≥ 231361) := by
  rcases imo1996_p4_assumed with ⟨⟨a, b, m, n, ha, hb, hm, hn, hab, hsub, hl⟩, hleast⟩
  have ha0 : 0 ≤ a := ha.le
  have hb0 : 0 ≤ b := hb.le
  have hm0 : 0 ≤ m := hm.le
  have hn0 : 0 ≤ n := hn.le
  have hba : 15 * b ≤ 16 * a := by nlinarith [sq_nonneg n]
  refine ⟨?_, ?_⟩
  · refine ⟨a.toNat, b.toNat, m.toNat, n.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · apply Nat.cast_injective (R := ℤ)
      push_cast
      simpa [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0,
        Int.toNat_of_nonneg hm0] using hab
    · have hba' : 15 * b.toNat ≤ 16 * a.toNat := by omega
      apply Nat.sub_eq_iff_eq_add hba' |>.2
      apply Nat.cast_injective (R := ℤ)
      push_cast
      simp [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0,
        Int.toNat_of_nonneg hn0]
      nlinarith [hsub]
    · apply Nat.cast_injective (R := ℤ)
      push_cast
      simpa [solution, Int.toNat_of_nonneg hm0, Int.toNat_of_nonneg hn0] using hl.symm
  · intro A B X Y h
    rcases h with ⟨hA, hB, hX, hY, hAB, hXY⟩
    have hBA : 15 * B ≤ 16 * A := by
      by_contra hnle
      have : 16 * A - 15 * B = 0 := Nat.sub_eq_zero_of_le (by omega)
      nlinarith
    have hzsub : (16 : ℤ) * A - 15 * B = Y ^ 2 := by
      rw [sub_eq_iff_eq_add]
      exact_mod_cast (Nat.sub_eq_iff_eq_add hBA |>.1 hXY)
    have hzmem : ((min (X ^ 2) (Y ^ 2) : ℕ) : ℤ) ∈ S := by
      refine ⟨A, B, X, Y, by exact_mod_cast hA, by exact_mod_cast hB,
        by exact_mod_cast hX, by exact_mod_cast hY, by exact_mod_cast hAB, hzsub, ?_⟩
      norm_cast
    have hz := hleast _ hzmem
    change (231361 : ℤ) ≤ ↑(min (X ^ 2) (Y ^ 2)) at hz
    exact_mod_cast hz
