import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℕ) [Fact p.Prime] : (∃ n, n = (p - 1) / 2 ∧ (∃ (quadratic_residues : Finset (ZMod p)) (quadratic_nonresidues : Finset (ZMod p)), quadratic_residues.card = n ∧ quadratic_nonresidues.card = n ∧ ∀ x : ZMod p, x ≠ 0 → (x ∈ quadratic_residues ∨ x ∈ quadratic_nonresidues) ∧ (x ∈ quadratic_residues ↔ ¬ (x ∈ quadratic_nonresidues)))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_9 (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  -- not proved: the candidate gives no quadratic-residue property for either set
  sorry
