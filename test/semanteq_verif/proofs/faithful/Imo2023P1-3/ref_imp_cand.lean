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
  · rintro ⟨hn, hnprime, hprop⟩
    have hnmem : n ∈ ({n | 1 < n ∧ ¬n.Prime ∧ Dividable n} : Set ℕ) := by
      refine ⟨hn, hnprime, ?_⟩
      intro a b c habc
      exact hprop.2.2 a b c
        ⟨habc.1.1, habc.1.2.1, habc.2.2.1, habc.1.2.2.1, habc.2.2.2.1⟩
    have hpp : IsPrimePow n := (show n ∈ solution_set from
      imo2023_p1_assumed.symm ▸ hnmem).2
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hpp
    refine ⟨p, k, hp, ?_, hpk.symm⟩
    have hk1 : k ≠ 1 := by
      intro hkone
      subst k
      simp only [pow_one] at hpk
      exact hnprime (hpk ▸ hp)
    omega
  · rintro ⟨p, k, hp, hk, rfl⟩
    have hnprime : ¬Nat.Prime (p ^ k) := fun h => h.not_prime_pow hk
    have hpp : IsPrimePow (p ^ k) :=
      (isPrimePow_nat_iff (p ^ k)).2 ⟨p, k, hp, by omega, rfl⟩
    have href : 1 < p ^ k ∧ ¬Nat.Prime (p ^ k) ∧ Dividable (p ^ k) := by
      have : p ^ k ∈ solution_set := ⟨hnprime, hpp⟩
      exact (show p ^ k ∈ ({n | 1 < n ∧ ¬n.Prime ∧ Dividable n} : Set ℕ) from
        imo2023_p1_assumed ▸ this)
    refine ⟨href.1, href.2.1, href.1, href.2.1, ?_⟩
    intro d₁ d₂ d₃ hd
    rcases hd with ⟨hd₁, hd₂, hd₃, hd₁₂, hd₂₃⟩
    obtain ⟨i, hi, hd₁eq⟩ := (Nat.dvd_prime_pow hp).mp hd₁
    obtain ⟨j, hj, hd₂eq⟩ := (Nat.dvd_prime_pow hp).mp hd₂
    obtain ⟨l, hl, hd₃eq⟩ := (Nat.dvd_prime_pow hp).mp hd₃
    have hij : i ≤ j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (hd₁eq ▸ hd₂eq ▸ hd₁₂) |>.le
    have hil : i ≤ l := (Nat.pow_lt_pow_iff_right hp.one_lt).mp
      (hd₁eq ▸ hd₃eq ▸ hd₁₂.trans hd₂₃) |>.le
    rw [hd₁eq, hd₂eq, hd₃eq]
    exact dvd_add (pow_dvd_pow p hij) (pow_dvd_pow p hil)
