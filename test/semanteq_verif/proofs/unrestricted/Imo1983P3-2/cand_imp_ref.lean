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
  rcases problem_statement_assumed a b c ha hb hc hab hbc hca with ⟨hbad, hall⟩
  let d : ℕ := 2 * a * b * c - a * b - b * c - c * a
  have hd0 : d ≠ 0 := by
    intro hd
    apply hbad
    refine ⟨0, 0, 0, ?_⟩
    simpa [d] using hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have h₁ : a * b ≤ 2 * a * b * c := by omega
  have h₂ : b * c ≤ 2 * a * b * c - a * b := by omega
  have h₃ : c * a ≤ 2 * a * b * c - a * b - b * c := by omega
  have hdcast : (d : ℤ) = 2 * a * b * c - a * b - b * c - c * a := by
    simp [d, Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃]
  constructor
  · change ¬∃ x y z : ℕ,
      (2 * a * b * c - a * b - b * c - c * a : ℤ) =
        x * (b * c) + y * (c * a) + z * (a * b)
    rintro ⟨x, y, z, hxyz⟩
    apply hbad
    refine ⟨x, y, z, ?_⟩
    have hnat : d = x * (b * c) + y * (c * a) + z * (a * b) := by
      exact_mod_cast hdcast.trans hxyz
    simpa [d, mul_assoc] using hnat
  · intro n hn
    change n ≤ (2 * a * b * c - a * b - b * c - c * a : ℤ)
    rw [← hdcast]
    by_contra hle
    have hdn : (d : ℤ) < n := lt_of_not_ge hle
    have hn0 : 0 ≤ n := le_trans (Int.ofNat_zero.le.trans (Int.ofNat_le.mpr (Nat.zero_le d))) hdn.le
    let k : ℕ := n.toNat
    have hnk : (k : ℤ) = n := by simp [k, Int.toNat_of_nonneg hn0]
    have hdk : d < k := by exact_mod_cast (hnk.symm ▸ hdn)
    rcases hall k hdk with ⟨x, y, z, hk⟩
    apply hn
    refine ⟨x, y, z, ?_⟩
    rw [← hnk]
    exact_mod_cast (show k = x * (b * c) + y * (c * a) + z * (a * b) by
      simpa [mul_assoc] using hk)
