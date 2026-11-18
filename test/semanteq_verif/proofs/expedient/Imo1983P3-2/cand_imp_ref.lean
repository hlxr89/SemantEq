import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hab : Nat.gcd a b = 1) (hbc : Nat.gcd b c = 1) (hca : Nat.gcd c a = 1) :
  (¬ ∃ (x y z : ℕ), 2 * a * b * c - a * b - b * c - c * a = x * b * c + y * c * a + z * a * b) ∧
  (∀ n : ℕ, n > 2 * a * b * c - a * b - b * c - c * a → ∃ (x y z : ℕ), n = x * b * c + y * c * a + z * a * b) :=
by sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1983_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest
      {n : ℤ | ¬∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) := by
  have h := problem_statement_assumed a b c ha hb hc hab.gcd_eq_one hbc.gcd_eq_one hca.gcd_eq_one
  have hadd_le_mul {u v : ℕ} (hu : 2 ≤ u) (hv : 2 ≤ v) : u + v ≤ u * v := by
    nlinarith [Nat.zero_le ((u - 2) * (v - 2))]
  have hab1 : ¬(a = 1 ∧ b = 1) := by
    rintro ⟨rfl, rfl⟩
    apply h.1
    exact ⟨0, 0, 0, by omega⟩
  have hbc1 : ¬(b = 1 ∧ c = 1) := by
    rintro ⟨rfl, rfl⟩
    apply h.1
    exact ⟨0, 0, 0, by omega⟩
  have hca1 : ¬(c = 1 ∧ a = 1) := by
    rintro ⟨rfl, rfl⟩
    apply h.1
    exact ⟨0, 0, 0, by omega⟩
  have hsum : a * b + b * c + c * a ≤ 2 * a * b * c := by
    rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
    · have hb2 : 2 ≤ b := by omega
      have hc2 : 2 ≤ c := by omega
      have := hadd_le_mul hb2 hc2
      norm_num at *
      nlinarith
    · rcases (show b = 1 ∨ 2 ≤ b by omega) with rfl | hb2
      · have hc2 : 2 ≤ c := by omega
        have := hadd_le_mul hc2 ha2
        norm_num at *
        nlinarith
      · have := hadd_le_mul ha2 hb2
        nlinarith
  have h₁ : a * b ≤ 2 * a * b * c := by omega
  have h₂ : b * c ≤ 2 * a * b * c - a * b := by omega
  have h₃ : c * a ≤ 2 * a * b * c - a * b - b * c := by omega
  have hcast :
      ((2 * a * b * c - a * b - b * c - c * a : ℕ) : ℤ) =
        2 * a * b * c - a * b - b * c - c * a := by
    rw [Nat.cast_sub h₃, Nat.cast_sub h₂, Nat.cast_sub h₁]
    push_cast
    ring
  constructor
  · rintro ⟨x, y, z, hxyz⟩
    apply h.1
    refine ⟨x, y, z, ?_⟩
    rw [← hcast] at hxyz
    norm_cast at hxyz
    simpa [mul_assoc] using hxyz
  · intro n hn
    by_contra hle
    have hgt : (2 * a * b * c - a * b - b * c - c * a : ℤ) < n := by omega
    have hn0 : 0 ≤ n := by
      rw [← hcast] at hgt
      exact le_trans (Int.natCast_nonneg _) (le_of_lt hgt)
    let k : ℕ := n.toNat
    have hkcast : (k : ℤ) = n := by
      simp [k, Int.toNat_of_nonneg hn0]
    have hkgt : 2 * a * b * c - a * b - b * c - c * a < k := by
      exact_mod_cast (show
        ((2 * a * b * c - a * b - b * c - c * a : ℕ) : ℤ) < (k : ℤ) by
          rw [hcast, hkcast]
          exact hgt)
    obtain ⟨x, y, z, hxyz⟩ := h.2 k hkgt
    apply hn
    refine ⟨x, y, z, ?_⟩
    rw [← hkcast]
    norm_cast
    simpa [mul_assoc] using hxyz
