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
  · rintro ⟨hn, hnprime, hproperty⟩
    have hdividable : Dividable n := by
      intro a b c hconsecutive
      exact hproperty.2.2 a b c
        ⟨hconsecutive.1.1, hconsecutive.1.2.1, hconsecutive.2.2.1,
          hconsecutive.1.2.2.1, hconsecutive.2.2.2.1⟩
    have hsolution : n ∈ solution_set := by
      rw [imo2023_p1_assumed]
      exact ⟨hn, hnprime, hdividable⟩
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hsolution.2
    refine ⟨p, k, hp, ?_, hpk.symm⟩
    cases k with
    | zero => exact False.elim (Nat.lt_irrefl 0 hk)
    | succ k =>
        cases k with
        | zero =>
            exact False.elim (hnprime (by rw [← hpk]; simpa using hp))
        | succ k =>
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
  · rintro ⟨p, k, hp, hk, rfl⟩
    have hprimepow : IsPrimePow (p ^ k) :=
      (isPrimePow_nat_iff (p ^ k)).mpr ⟨p, k, hp, Nat.zero_lt_of_lt hk, rfl⟩
    have hsolution : p ^ k ∈ solution_set := ⟨Nat.Prime.not_prime_pow hk, hprimepow⟩
    have href : p ^ k ∈ { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
      rw [← imo2023_p1_assumed]
      exact hsolution
    refine ⟨href.1, href.2.1, href.1, href.2.1, ?_⟩
    intro d₁ d₂ d₃ hd
    obtain ⟨i, hi, hi_eq⟩ := (Nat.dvd_prime_pow hp).mp hd.1
    obtain ⟨j, hj, hj_eq⟩ := (Nat.dvd_prime_pow hp).mp hd.2.1
    obtain ⟨l, hl, hl_eq⟩ := (Nat.dvd_prime_pow hp).mp hd.2.2.1
    rw [hi_eq, hj_eq, hl_eq] at hd ⊢
    exact dvd_add
      (pow_dvd_pow p ((Nat.pow_lt_pow_iff_right hp.one_lt).mp hd.2.2.2.1).le)
      (pow_dvd_pow p ((Nat.pow_lt_pow_iff_right hp.one_lt).mp
        (lt_trans hd.2.2.2.1 hd.2.2.2.2)).le)
