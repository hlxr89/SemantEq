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
  rcases dummy_assumed (p := 2) (by decide) 1 (by omega) with
    ⟨g, hg, hstep, _, heven, _, _⟩
  have hg0 : g 0 ≥ 1 := by
    have h := heven 0
    norm_num at h ⊢
    omega
  have hinc := hstep 0 hg0
  have hdec := hg (show 0 < 1 by omega)
  norm_num at hinc hdec
  omega
