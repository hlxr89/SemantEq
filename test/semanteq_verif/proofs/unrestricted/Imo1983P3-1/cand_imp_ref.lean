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
  let target : ℕ := 2 * a * b * c - a * b - b * c - c * a
  have hcand := problem_statement_assumed a b c ha hb hc hab.gcd_eq_one hbc.gcd_eq_one hca.gcd_eq_one
  change (∀ n : ℕ, n > target → ∃ x y z : ℕ,
      n = x * b * c + y * c * a + z * a * b) ∧
    (∀ x y z : ℕ, x * b * c + y * c * a + z * a * b ≠ target) at hcand
  rcases hcand with ⟨hall, htarget⟩
  have ht_ne : target ≠ 0 := by
    intro ht
    apply htarget 0 0 0
    simp [ht]
  have ht_pos : 0 < target := Nat.pos_of_ne_zero ht_ne
  have hsub1 : a * b ≤ 2 * a * b * c := by omega
  have hsub2 : b * c ≤ 2 * a * b * c - a * b := by
    dsimp [target] at ht_pos
    omega
  have hsub3 : c * a ≤ 2 * a * b * c - a * b - b * c := by
    dsimp [target] at ht_pos
    omega
  have hcast : (target : ℤ) = 2 * a * b * c - a * b - b * c - c * a := by
    dsimp [target]
    push_cast [Nat.cast_sub hsub1, Nat.cast_sub hsub2, Nat.cast_sub hsub3]
    ring
  rw [← hcast]
  constructor
  · intro hrep
    rcases hrep with ⟨x, y, z, hxyz⟩
    apply htarget x y z
    have hxnat : target = x * (b * c) + y * (c * a) + z * (a * b) := by
      exact_mod_cast hxyz
    simpa [mul_assoc] using hxnat.symm
  · intro n hn
    by_contra hnot
    have hgt : (target : ℤ) < n := lt_of_not_ge hnot
    have hn_nonneg : 0 ≤ n := by
      have : (0 : ℤ) < target := by exact_mod_cast ht_pos
      omega
    let m : ℕ := n.toNat
    have hm_cast : (m : ℤ) = n := by
      dsimp [m]
      exact Int.toNat_of_nonneg hn_nonneg
    have hm_gt : m > target := by
      rw [← hm_cast] at hgt
      exact_mod_cast hgt
    rcases hall m hm_gt with ⟨x, y, z, hxyz⟩
    apply hn
    refine ⟨x, y, z, ?_⟩
    rw [← hm_cast]
    exact_mod_cast (show m = x * (b * c) + y * (c * a) + z * (a * b) by
      simpa [mul_assoc] using hxyz)
