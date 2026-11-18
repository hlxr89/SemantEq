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
  obtain ⟨hrep, hN⟩ := problem_statement_assumed a b c ha hb hc hab.gcd_eq_one hbc.gcd_eq_one hca.gcd_eq_one
  let N : ℕ := 2 * a * b * c - a * b - b * c - c * a
  have hsub : 2 * a * b * c - (a * b + b * c + c * a) = N := by
    simp only [N, Nat.sub_sub]
    rw [add_assoc]
  have hN0 : N ≠ 0 := by
    intro hz
    apply hN
    refine ⟨0, 0, 0, ?_⟩
    simpa only [zero_mul, zero_add, N] using hz
  have hle : a * b + b * c + c * a ≤ 2 * a * b * c := by
    -- non-rewrite step: nonrepresentability of N rules out truncated subtraction.
    apply Nat.le_of_lt
    apply Nat.sub_ne_zero_iff_lt.mp
    rw [hsub]
    exact hN0
  have hcast : (N : ℤ) = 2 * a * b * c - a * b - b * c - c * a := by
    rw [← hsub, Nat.cast_sub hle]
    push_cast
    rw [sub_sub, sub_sub, add_assoc]
  constructor
  · intro hrepr
    apply hN
    rcases hrepr with ⟨x, y, z, hxyz⟩
    refine ⟨x, y, z, ?_⟩
    rw [← Int.ofNat_inj, hcast]
    simpa only [Nat.cast_add, Nat.cast_mul, mul_assoc] using hxyz
  · intro n hn
    apply le_of_not_gt
    intro hlt
    rw [← hcast] at hlt
    have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg N) hlt.le
    have hnatlt : N < n.toNat := by
      rw [← Int.ofNat_lt]
      simpa only [Int.toNat_of_nonneg hn0] using hlt
    obtain ⟨x, y, z, hxyz⟩ := hrep n.toNat hnatlt
    apply hn
    refine ⟨x, y, z, ?_⟩
    rw [← Int.toNat_of_nonneg hn0, hxyz]
    push_cast
    simp only [mul_assoc]
