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
  have hright := (problem_statement_assumed 0).mp (by
    intro h
    omega)
  rcases hright with ⟨p, k, hp, hk, hzero⟩
  have hne : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  exact (hne hzero.symm).elim

