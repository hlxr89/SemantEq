import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hab : Nat.gcd a b = 1) (hbc : Nat.gcd b c = 1) (hca : Nat.gcd c a = 1) :
  let target := 2 * a * b * c - a * b - b * c - c * a
  (∀ n : ℕ, n > target → ∃ x y z : ℕ, n = x * b * c + y * c * a + z * a * b) ∧
  (∀ x y z : ℕ, x * b * c + y * c * a + z * a * b ≠ target) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1983_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest
      {n : ℤ | ¬∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) := by
  have h := problem_statement_assumed a b c ha hb hc
    (Nat.coprime_iff_gcd_eq_one.mp hab)
    (Nat.coprime_iff_gcd_eq_one.mp hbc)
    (Nat.coprime_iff_gcd_eq_one.mp hca)
  dsimp only at h
  have htarget_ne : 2 * a * b * c - a * b - b * c - c * a ≠ 0 := by
    intro hzero
    apply h.2 0 0 0
    simp only [zero_mul, zero_add]
    exact hzero.symm
  have htarget_pos : 0 < 2 * a * b * c - a * b - b * c - c * a :=
    Nat.pos_of_ne_zero htarget_ne
  have hca_le : c * a ≤ 2 * a * b * c - a * b - b * c :=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp htarget_pos)
  have habc_pos : 0 < 2 * a * b * c - a * b - b * c :=
    lt_of_le_of_lt (Nat.zero_le (c * a)) (Nat.sub_pos_iff_lt.mp htarget_pos)
  have hbc_le : b * c ≤ 2 * a * b * c - a * b :=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp habc_pos)
  have hab_pos : 0 < 2 * a * b * c - a * b :=
    lt_of_le_of_lt (Nat.zero_le (b * c)) (Nat.sub_pos_iff_lt.mp habc_pos)
  have hab_le : a * b ≤ 2 * a * b * c :=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hab_pos)
  have hcast :
      ((2 * a * b * c - a * b - b * c - c * a : ℕ) : ℤ) =
        2 * a * b * c - a * b - b * c - c * a := by
    rw [Nat.cast_sub hca_le, Nat.cast_sub hbc_le, Nat.cast_sub hab_le]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · rintro ⟨x, y, z, heq⟩
    apply h.2 x y z
    have hnat :
        2 * a * b * c - a * b - b * c - c * a =
          x * (b * c) + y * (c * a) + z * (a * b) := by
      apply Int.ofNat_inj.mp
      simp only [Nat.cast_add, Nat.cast_mul]
      rw [hcast]
      exact heq
    simpa only [Nat.mul_assoc] using hnat.symm
  · intro n hn
    rw [← hcast]
    apply le_of_not_gt
    intro hgt
    have hn_nonneg : 0 ≤ n :=
      le_trans (Int.ofNat_zero_le _) (le_of_lt hgt)
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn_nonneg
    have hkgt : 2 * a * b * c - a * b - b * c - c * a < k := by
      exact_mod_cast hgt
    obtain ⟨x, y, z, hk⟩ := h.1 k hkgt
    apply hn
    refine ⟨x, y, z, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.mul_assoc] using congrArg (fun m : ℕ => (m : ℤ)) hk
