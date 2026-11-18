import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {x : G} {n : ℕ} (hx : orderOf x = n) (H : Subgroup G) : (∃ p : ℕ, p.Prime ∧ H = Subgroup.zpowers (x ^ (n / p)) ∧ p ∣ n) ↔ (∀ K : Subgroup G, H ≤ K → K = ⊤ ∨ K = H) := sorry
