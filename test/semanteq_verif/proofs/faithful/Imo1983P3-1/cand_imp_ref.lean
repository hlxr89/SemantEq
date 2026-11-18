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
  have h := problem_statement_assumed a b c ha hb hc hab.gcd_eq_one hbc.gcd_eq_one hca.gcd_eq_one
  change
    (∀ n : ℕ, n > target → ∃ x y z : ℕ, n = x * b * c + y * c * a + z * a * b) ∧
      (∀ x y z : ℕ, x * b * c + y * c * a + z * a * b ≠ target) at h
  rcases h with ⟨hlarge, htarget⟩
  have htpos : 0 < target := by
    have := htarget 0 0 0
    simp only [zero_mul, zero_add] at this
    omega
  have hnat_eq : target + a * b + b * c + c * a = 2 * a * b * c := by
    dsimp [target] at htpos ⊢
    omega
  have hcast : (target : ℤ) = 2 * a * b * c - a * b - b * c - c * a := by
    have hz := congrArg (fun n : ℕ => (n : ℤ)) hnat_eq
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz ⊢
    omega
  rw [← hcast]
  constructor
  · intro hrep
    rcases hrep with ⟨x, y, z, hxyz⟩
    apply htarget x y z
    have heq : x * (b * c) + y * (c * a) + z * (a * b) = target := by
      exact_mod_cast hxyz.symm
    simpa only [Nat.mul_assoc] using heq
  · intro n hn
    by_cases hnneg : n < 0
    · omega
    · have hnnonneg : 0 ≤ n := le_of_not_gt hnneg
      apply le_of_not_gt
      intro hgt
      have hnatgt : n.toNat > target := by
        rw [← Int.toNat_of_nonneg hnnonneg] at hgt
        exact_mod_cast hgt
      rcases hlarge n.toNat hnatgt with ⟨x, y, z, hxyz⟩
      apply hn
      use x, y, z
      rw [← Int.toNat_of_nonneg hnnonneg]
      have hxyz' : n.toNat = x * (b * c) + y * (c * a) + z * (a * b) := by
        simpa only [Nat.mul_assoc] using hxyz
      exact_mod_cast hxyz'
