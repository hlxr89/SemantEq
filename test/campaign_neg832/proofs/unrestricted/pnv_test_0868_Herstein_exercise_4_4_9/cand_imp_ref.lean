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
  obtain ⟨R, hcard, hR⟩ := dummy_assumed hp
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  have hhalf : 0 < Nat.div (p - 1) 2 := by
    apply Nat.div_pos
    · omega
    · omega
  have hRpos : 0 < R.card := by
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hRpos
  exact False.elim ((hR i hi i hi).1 (Nat.ModEq.refl i))
