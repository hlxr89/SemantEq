import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution : ℤ := 231361

def S := { l | ∃ a b m n : ℤ,
    0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < n ∧
    15*a + 16*b = m^2 ∧
    16*a - 15*b = n^2 ∧
    l = min (m^2) (n^2) }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
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
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1996_p4 : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  rcases problem_statement_assumed with ⟨⟨a, b, m, n, ha, hb, hm, hn, hab, hsub, hl⟩, hleast⟩
  have hba : 15 * b ≤ 16 * a := by
    by_contra hnle
    have : 16 * a - 15 * b = 0 := Nat.sub_eq_zero_of_le (by omega)
    nlinarith
  have hzsub : (16 : ℤ) * a - 15 * b = n ^ 2 := by
    rw [sub_eq_iff_eq_add]
    exact_mod_cast (Nat.sub_eq_iff_eq_add hba |>.1 hsub)
  refine ⟨?_, ?_⟩
  · refine ⟨a, b, m, n, by exact_mod_cast ha, by exact_mod_cast hb,
      by exact_mod_cast hm, by exact_mod_cast hn, by exact_mod_cast hab, hzsub, ?_⟩
    norm_num [solution]
    exact_mod_cast hl.symm
  · intro l hlS
    rcases hlS with ⟨A, B, X, Y, hA, hB, hX, hY, hAB, hXY, rfl⟩
    have hA0 : 0 ≤ A := hA.le
    have hB0 : 0 ≤ B := hB.le
    have hX0 : 0 ≤ X := hX.le
    have hY0 : 0 ≤ Y := hY.le
    have hBA : 15 * B ≤ 16 * A := by nlinarith [sq_nonneg Y]
    have hnAB : 15 * A.toNat + 16 * B.toNat = X.toNat ^ 2 := by
      apply Nat.cast_injective (R := ℤ)
      push_cast
      simpa [Int.toNat_of_nonneg hA0, Int.toNat_of_nonneg hB0,
        Int.toNat_of_nonneg hX0] using hAB
    have hnXY : 16 * A.toNat - 15 * B.toNat = Y.toNat ^ 2 := by
      have hBA' : 15 * B.toNat ≤ 16 * A.toNat := by omega
      apply Nat.sub_eq_iff_eq_add hBA' |>.2
      apply Nat.cast_injective (R := ℤ)
      push_cast
      simp [Int.toNat_of_nonneg hA0, Int.toNat_of_nonneg hB0,
        Int.toNat_of_nonneg hY0]
      nlinarith [hXY]
    have hnmin := hleast A.toNat B.toNat X.toNat Y.toNat
      ⟨by omega, by omega, by omega, by omega, hnAB, hnXY⟩
    have hz : (231361 : ℤ) ≤ ((min (X.toNat ^ 2) (Y.toNat ^ 2) : ℕ) : ℤ) := by
      exact_mod_cast hnmin
    simpa [solution, Int.toNat_of_nonneg hX0, Int.toNat_of_nonneg hY0] using hz
