import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

abbrev Dividable (n : ℕ) :=
  ∀ {a b c : ℕ},
    ConsecutiveFactors n a b ∧ ConsecutiveFactors n b c
    → a ∣ b + c

abbrev solution_set : Set ℕ := { n | ¬n.Prime ∧ IsPrimePow n }

noncomputable def has_divisor_property (n : ℕ) : Prop :=
  n > 1 ∧ ¬ Nat.Prime n ∧
  ∀ d₁ d₂ d₃ : ℕ,
    d₁ ∣ n ∧ d₂ ∣ n ∧ d₃ ∣ n ∧
    d₁ < d₂ ∧ d₂ < d₃ →
    d₁ ∣ (d₂ + d₃)

-- ===== assumed statement (antecedent) =====
theorem imo2023_p1_assumed : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) :
  (n > 1 ∧ ¬ Nat.Prime n ∧ has_divisor_property n) ↔
  ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 2 ∧ n = p ^ k := by
  constructor
  · rintro ⟨hn, hnprime, ⟨_, _, hdivs⟩⟩
    have hdividable : Dividable n := by
      rintro a b c ⟨⟨ha, hb, hab, _⟩, ⟨_, hc, hbc, _⟩⟩
      exact hdivs a b c ⟨ha, hb, hc, hab, hbc⟩
    have hnmem : n ∈ solution_set := by
      rw [imo2023_p1_assumed]
      exact ⟨hn, hnprime, hdividable⟩
    rcases hnmem.2 with ⟨p, k, hp, hk, hpow⟩
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k = 1 := by omega
      subst k
      simp only [pow_one] at hpow
      exact hnprime (hpow ▸ Nat.prime_iff.mpr hp)
    exact ⟨p, k, Nat.prime_iff.mpr hp, hk2, hpow.symm⟩
  · rintro ⟨p, k, hp, hk, rfl⟩
    have hk0 : k ≠ 0 := by omega
    have hn : p ^ k > 1 := Nat.one_lt_pow hk0 hp.one_lt
    have hnprime : ¬Nat.Prime (p ^ k) := Nat.Prime.not_prime_pow hk
    refine ⟨hn, hnprime, hn, hnprime, ?_⟩
    intro d₁ d₂ d₃ h
    rcases h with ⟨hd₁, hd₂, hd₃, hd₁₂, hd₂₃⟩
    rcases (Nat.dvd_prime_pow hp).mp hd₁ with ⟨i, hi, rfl⟩
    rcases (Nat.dvd_prime_pow hp).mp hd₂ with ⟨j, hj, rfl⟩
    rcases (Nat.dvd_prime_pow hp).mp hd₃ with ⟨l, hl, rfl⟩
    have hij : i < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hd₁₂
    have hil : i < l :=
      (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_trans hd₁₂ hd₂₃)
    exact dvd_add (pow_dvd_pow p hij.le) (pow_dvd_pow p hil.le)
