import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_4_9_assumed (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {p : ℕ} (hp : Nat.Prime p) : (∃ (res nonres : Finset (ZMod p)), res.card = (p - 1) / 2 ∧ nonres.card = (p - 1) / 2 ∧ (∀ a ∈ res, ∃ b : ZMod p, b^2 = a) ∧ (∀ a ∈ nonres, ∀ b : ZMod p, b^2 ≠ a) ∧ ∀ x : ZMod p, x ≠ 0 → (x ∈ res ∨ x ∈ nonres)) := by
  -- not proved: for p = 2 the candidate conclusion is false, while the antecedent only applies to odd primes
  sorry
