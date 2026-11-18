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
  let N := 2 * a * b * c - a * b - b * c - c * a
  have h := problem_statement_assumed a b c ha hb hc hab.gcd_eq_one hbc.gcd_eq_one hca.gcd_eq_one
  dsimp only at h
  have hN_ne : N ≠ 0 := by
    intro hN
    apply h.2
    refine ⟨0, 0, 0, ?_⟩
    simpa only [zero_mul, zero_add, N] using hN
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN_ne
  have h₁ : a * b ≤ 2 * a * b * c := by
    dsimp only [N] at hN_pos
    omega
  have h₂ : b * c ≤ 2 * a * b * c - a * b := by
    dsimp only [N] at hN_pos
    omega
  have h₃ : c * a ≤ 2 * a * b * c - a * b - b * c := by
    dsimp only [N] at hN_pos
    omega
  have hcast : (N : ℤ) = 2 * a * b * c - a * b - b * c - c * a := by
    simp only [N, Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃, Nat.cast_mul,
      Nat.cast_ofNat]
  constructor
  · intro hex
    obtain ⟨x, y, z, hxyz⟩ := hex
    apply h.2
    refine ⟨x, y, z, ?_⟩
    rw [← hcast] at hxyz
    have hnat : N = x * (b * c) + y * (c * a) + z * (a * b) := by
      exact_mod_cast hxyz
    simpa only [N, mul_assoc] using hnat
  · intro n hn
    apply le_of_not_gt
    intro hnN
    have hnN' : (N : ℤ) < n := by simpa only [hcast] using hnN
    have hn_nonneg : 0 ≤ n := le_trans (Int.natCast_nonneg N) (le_of_lt hnN')
    let m := n.toNat
    have hmcast : (m : ℤ) = n := by
      exact Int.toNat_of_nonneg hn_nonneg
    have hmN : N < m := by
      exact_mod_cast (show (N : ℤ) < (m : ℤ) by simpa only [hmcast] using hnN')
    obtain ⟨x, y, z, hxyz⟩ := h.1 m hmN
    apply hn
    refine ⟨x, y, z, ?_⟩
    rw [← hmcast]
    have hnat : m = x * (b * c) + y * (c * a) + z * (a * b) := by
      simpa only [mul_assoc] using hxyz
    exact_mod_cast hnat
