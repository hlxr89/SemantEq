import Mathlib

open scoped BigOperators

theorem dummy {a : ℝ} (seq : ℕ → ℝ) (hseq : seq 0 = 0) : ∃ N, ∀ n ≥ N, seq (n + 2) = seq n ∧ seq (n + 1) = seq (n + 1) ∧ seq n = seq (n - 1) := sorry
