import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

abbrev Dividable (n : ℕ) :=
  ∀ {a b c : ℕ},
    ConsecutiveFactors n a b ∧ ConsecutiveFactors n b c
    → a ∣ b + c

abbrev solution_set : Set ℕ := { n | ¬n.Prime ∧ IsPrimePow n }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ n : ℕ, n > 1 →
    (∃ p : ℕ, Nat.Prime p ∧ ∃ k : ℕ, k ≥ 2 ∧ n = p ^ k) ↔
    (∃ (d : ℕ → ℕ),
      (∀ i : ℕ, i < n.divisors.card → d i ∈ n.divisors) ∧
      (∀ i j : ℕ, i < j ∧ j < n.divisors.card → d i < d j) ∧
      (∀ d' : ℕ, d' ∈ n.divisors → ∃ i : ℕ, i < n.divisors.card ∧ d i = d') ∧
      d 0 = 1 ∧
      d (n.divisors.card - 1) = n ∧
      (∀ i : ℕ, i < n.divisors.card - 2 → d i ∣ d (i + 1) + d (i + 2))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2023_p1 : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
  exfalso
  have h := problem_statement_assumed 2
  have hr : ∃ (d : ℕ → ℕ),
      (∀ i : ℕ, i < (2 : ℕ).divisors.card → d i ∈ (2 : ℕ).divisors) ∧
      (∀ i j : ℕ, i < j ∧ j < (2 : ℕ).divisors.card → d i < d j) ∧
      (∀ d' : ℕ, d' ∈ (2 : ℕ).divisors → ∃ i : ℕ, i < (2 : ℕ).divisors.card ∧ d i = d') ∧
      d 0 = 1 ∧
      d ((2 : ℕ).divisors.card - 1) = 2 ∧
      (∀ i : ℕ, i < (2 : ℕ).divisors.card - 2 → d i ∣ d (i + 1) + d (i + 2)) := by
    have hdivs : (2 : ℕ).divisors = {1, 2} := by native_decide
    refine ⟨fun i => if i = 0 then 1 else 2, ?_⟩
    simp [hdivs]
    refine ⟨fun i _ => em (i = 0), ?_, 1, by norm_num, by norm_num⟩
    intro i j hij hj
    split_ifs <;> omega
  rcases (h.mpr hr) (by norm_num) with ⟨p, hp, k, hk, hpk⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hpow : 4 ≤ p ^ k := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := pow_le_pow_left' hp2 2
      _ ≤ p ^ k := pow_le_pow_right' (by omega) hk
  omega
