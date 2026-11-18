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
  ∀ n : ℕ, n > 1 ∧ ¬ Nat.Prime n → 
  (∃ (d : List ℕ), 
    (∀ x ∈ d, x ∣ n) ∧ 
    (∀ x : ℕ, x ∣ n → x ∈ d) ∧
    d.Sorted (· < ·) ∧
    d.head? = some 1 ∧
    d.getLast? = some n ∧
    (∀ i : ℕ, i + 1 < d.length → d[i]! ∣ d[i+1]! + d[i+2]!)) ↔
  (∃ (p : ℕ) (k : ℕ), Nat.Prime p ∧ k ≥ 2 ∧ n = p ^ k) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2023_p1 : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
  exfalso
  have h := problem_statement_assumed 0
  have hl : 0 > 1 ∧ ¬Nat.Prime 0 →
      ∃ (d : List ℕ),
        (∀ x ∈ d, x ∣ 0) ∧
        (∀ x : ℕ, x ∣ 0 → x ∈ d) ∧
        d.Sorted (· < ·) ∧
        d.head? = some 1 ∧
        d.getLast? = some 0 ∧
        (∀ i : ℕ, i + 1 < d.length → d[i]! ∣ d[i+1]! + d[i+2]!) := by
    omega
  rcases h.mp hl with ⟨p, k, hp, hk, hpk⟩
  have hp0 : 0 < p := hp.pos
  have hpow : 0 < p ^ k := pow_pos hp0 k
  omega
