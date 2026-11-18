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
theorem dummy {p : ℕ} (hp : Fact p.Prime) : (∃ (S : Finset (ZMod p)), S.card = (p - 1) / 2) ∧ (∃ (T : Finset (ZMod p)), T.card = (p - 1) / 2) := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with rfl | hodd
  · exact ⟨⟨∅, by decide⟩, ⟨∅, by decide⟩⟩
  · rcases exercise_4_4_9_assumed p Fact.out hodd with
      ⟨⟨S, _, hS, _⟩, ⟨T, _, hT, _⟩⟩
    exact ⟨⟨S, hS⟩, ⟨T, hT⟩⟩
