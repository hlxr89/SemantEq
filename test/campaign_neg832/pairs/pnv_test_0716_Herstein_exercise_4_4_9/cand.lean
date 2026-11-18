import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {p : ℕ} (hp : Fact p.Prime) : (∃ (S : Finset (ZMod p)), S.card = (p - 1) / 2) ∧ (∃ (T : Finset (ZMod p)), T.card = (p - 1) / 2) := sorry
