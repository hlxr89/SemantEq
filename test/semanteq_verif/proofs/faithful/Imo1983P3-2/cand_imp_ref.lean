import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hab : Nat.gcd a b = 1) (hbc : Nat.gcd b c = 1) (hca : Nat.gcd c a = 1) :
  (¬ ∃ (x y z : ℕ), 2 * a * b * c - a * b - b * c - c * a = x * b * c + y * c * a + z * a * b) ∧
  (∀ n : ℕ, n > 2 * a * b * c - a * b - b * c - c * a → ∃ (x y z : ℕ), n = x * b * c + y * c * a + z * a * b) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1983_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest
      {n : ℤ | ¬∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) := by
  have h := problem_statement_assumed a b c ha hb hc hab.gcd_eq_one hbc.gcd_eq_one hca.gcd_eq_one
  have hpos : 0 < 2 * a * b * c - a * b - b * c - c * a := by
    have hne : 2 * a * b * c - a * b - b * c - c * a ≠ 0 := by
      intro heq
      apply h.1
      refine ⟨0, 0, 0, ?_⟩
      simp [heq]
    omega
  have hcast :
      ((2 * a * b * c - a * b - b * c - c * a : ℕ) : ℤ) =
        2 * a * b * c - a * b - b * c - c * a := by
    have h₁ : a * b ≤ 2 * a * b * c := by omega
    have h₂ : b * c ≤ 2 * a * b * c - a * b := by omega
    have h₃ : c * a ≤ 2 * a * b * c - a * b - b * c := by omega
    rw [Nat.cast_sub h₃, Nat.cast_sub h₂, Nat.cast_sub h₁]
    push_cast
    ring
  constructor
  · intro hrep
    apply h.1
    obtain ⟨x, y, z, hxyz⟩ := hrep
    refine ⟨x, y, z, ?_⟩
    rw [← hcast] at hxyz
    have hnat :
        2 * a * b * c - a * b - b * c - c * a =
          x * (b * c) + y * (c * a) + z * (a * b) := by
      exact_mod_cast hxyz
    simpa [Nat.mul_assoc] using hnat
  · intro n hn
    apply le_of_not_gt
    intro hgt
    rw [← hcast] at hgt
    have hn_nonneg : 0 ≤ n := le_trans (Int.natCast_nonneg _) (le_of_lt hgt)
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn_nonneg
    have hk : 2 * a * b * c - a * b - b * c - c * a < k := by
      exact_mod_cast hgt
    obtain ⟨x, y, z, hxyz⟩ := h.2 k hk
    apply hn
    refine ⟨x, y, z, ?_⟩
    exact_mod_cast (show k = x * (b * c) + y * (c * a) + z * (a * b) by
      simpa [Nat.mul_assoc] using hxyz)
