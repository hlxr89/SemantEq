import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {x : G} {n : ℕ} (hx : orderOf x = n) (H : Subgroup G) : (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = ⊤ ∨ K = H) ↔ ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ H = Subgroup.zpowers (x ^ (n / p)) := sorry
