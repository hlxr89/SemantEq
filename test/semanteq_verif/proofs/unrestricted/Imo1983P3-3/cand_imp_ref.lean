import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hab : Nat.gcd a b = 1) (hbc : Nat.gcd b c = 1) (hca : Nat.gcd c a = 1) :
  let N := 2 * a * b * c - a * b - b * c - c * a
  (∀ n : ℕ, N < n → ∃ x y z : ℕ, n = x * b * c + y * c * a + z * a * b) ∧
  (¬ ∃ x y z : ℕ, N = x * b * c + y * c * a + z * a * b) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1983_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest
      {n : ℤ | ¬∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) := by
  obtain ⟨hall, hN⟩ := problem_statement_assumed a b c ha hb hc hab.gcd_eq_one
    hbc.gcd_eq_one hca.gcd_eq_one
  have hNpos : 0 < 2 * a * b * c - a * b - b * c - c * a := by
    by_contra h
    have hz : 2 * a * b * c - a * b - b * c - c * a = 0 := Nat.eq_zero_of_not_pos h
    apply hN
    exact ⟨0, 0, 0, by simp [hz]⟩
  have h₁ : a * b ≤ 2 * a * b * c := by omega
  have h₂ : b * c ≤ 2 * a * b * c - a * b := by omega
  have h₃ : c * a ≤ 2 * a * b * c - a * b - b * c := by omega
  have hcast :
      ((2 * a * b * c - a * b - b * c - c * a : ℕ) : ℤ) =
        2 * a * b * c - a * b - b * c - c * a := by
    simp only [Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃, Nat.cast_mul,
      Nat.cast_ofNat]
  constructor
  · rintro ⟨x, y, z, heq⟩
    apply hN
    refine ⟨x, y, z, ?_⟩
    rw [← hcast] at heq
    simpa only [mul_assoc] using (show
      2 * a * b * c - a * b - b * c - c * a =
        x * (b * c) + y * (c * a) + z * (a * b) by exact_mod_cast heq)
  · intro n hn
    by_contra hle
    have hlt : (2 * a * b * c - a * b - b * c - c * a : ℤ) < n :=
      lt_of_not_ge hle
    have hn0 : 0 ≤ n := by
      rw [← hcast] at hlt
      omega
    have hlt' : 2 * a * b * c - a * b - b * c - c * a < n.toNat := by
      rw [← hcast] at hlt
      rw [← Int.toNat_of_nonneg hn0] at hlt
      exact_mod_cast hlt
    obtain ⟨x, y, z, heq⟩ := hall n.toNat hlt'
    apply hn
    refine ⟨x, y, z, ?_⟩
    rw [← Int.toNat_of_nonneg hn0]
    exact_mod_cast (show
      n.toNat = x * (b * c) + y * (c * a) + z * (a * b) by
        simpa only [mul_assoc] using heq)
