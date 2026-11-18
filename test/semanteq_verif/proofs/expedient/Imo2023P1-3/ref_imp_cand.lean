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
  · rintro ⟨hn, hnp, h⟩
    have hd : Dividable n := by
      intro a b c hab
      exact h.2.2 a b c ⟨hab.1.1, hab.1.2.1, hab.2.2.1,
        hab.1.2.2.1, hab.2.2.2.1⟩
    have hm : n ∈ solution_set := by
      rw [imo2023_p1_assumed]
      exact ⟨hn, hnp, hd⟩
    obtain ⟨p, k, hp, hk, heq⟩ := (isPrimePow_nat_iff n).1 hm.2
    refine ⟨p, k, hp, ?_, heq.symm⟩
    by_contra hnk
    interval_cases k <;> simp_all
  · rintro ⟨p, k, hp, hk, rfl⟩
    have hnp : ¬Nat.Prime (p ^ k) := Nat.Prime.not_prime_pow hk
    have hone : 1 < p ^ k := (hp.isPrimePow.pow (by omega)).one_lt
    refine ⟨hone, hnp, by
      refine ⟨hone, hnp, ?_⟩
      intro d₁ d₂ d₃ h
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 h.1
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).1 h.2.1
      obtain ⟨l, hl, rfl⟩ := (Nat.dvd_prime_pow hp).1 h.2.2.1
      have hij : i ≤ j := by
        by_contra hnij
        have hji : j < i := Nat.lt_of_not_ge hnij
        have := Nat.pow_le_pow_right hp.pos (Nat.le_of_lt hji)
        omega
      have hil : i ≤ l := by
        by_contra hnil
        have hli : l < i := Nat.lt_of_not_ge hnil
        have := Nat.pow_le_pow_right hp.pos (Nat.le_of_lt hli)
        omega
      exact Nat.dvd_add (Nat.pow_dvd_pow p hij) (Nat.pow_dvd_pow p hil)
    ⟩
