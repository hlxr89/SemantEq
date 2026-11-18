import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : Nat.Prime p) : ∃ (R : Finset ℕ), R.card = Nat.div (p - 1) 2 ∧ ∀ i ∈ R, ∀ j ∈ R, ¬i ≡ j [MOD p] ∧ ∀ j : ℕ, ¬j ∈ R → ∃ (x : ℕ), x^2 ≡ j [MOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_9 (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  -- not proved: the candidate assumption is inconsistent for odd p, so it cannot transport evidence for the reference witnesses without forbidden ex-falso reasoning
  sorry
