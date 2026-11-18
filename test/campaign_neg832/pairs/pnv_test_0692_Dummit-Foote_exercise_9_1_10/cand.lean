import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {p : ℕ} (hp : Prime p) (k : ℕ) (hk : k ≥ 1) : ∃ (f : ℕ → ℕ) (H : StrictAnti f), (∀ (i : ℕ), f i ≥ 1 → f (i + 1) ≥ f i + 1) ∧ (∀ (i : ℕ), f i ≥ 1 → f (i + 1) ≥ f i + 2) ∧ (∀ (i : ℕ), f (2 * i) ≥ p ^ 2) ∧ (∀ (i : ℕ), f (2 * i + 1) ≥ p ^ 2) ∧ ∀ (i : ℕ), i ≥ k → p ∣ f i := sorry
