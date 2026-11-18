import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : Prime p) (k : ℕ) (hk : k ≥ 1) : ∃ (f : ℕ → ℕ) (H : StrictAnti f), (∀ (i : ℕ), f i ≥ 1 → f (i + 1) ≥ f i + 1) ∧ (∀ (i : ℕ), f i ≥ 1 → f (i + 1) ≥ f i + 2) ∧ (∀ (i : ℕ), f (2 * i) ≥ p ^ 2) ∧ (∀ (i : ℕ), f (2 * i + 1) ≥ p ^ 2) ∧ ∀ (i : ℕ), i ≥ k → p ∣ f i := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_1_10 {f : ℕ → MvPolynomial ℕ ℤ}
  (hf : f = λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)):
  Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) := by
  obtain ⟨g, hg, _⟩ := dummy_assumed Nat.prime_two.prime 1 (by omega)
  exfalso
  have hbound : ∀ n : ℕ, g n + n ≤ g 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hdec : g (n + 1) < g n := hg (Nat.lt_succ_self n)
      omega
  have := hbound (g 0 + 1)
  omega
