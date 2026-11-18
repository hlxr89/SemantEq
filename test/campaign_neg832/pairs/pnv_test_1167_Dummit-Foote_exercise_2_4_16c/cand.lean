import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {x : G} {n : ℕ} (hx : x ^ n = 1) (H : Subgroup G) : (∃ k : ℕ, k ∣ n ∧ H = Subgroup.closure ({x ^ k} : Set G) ∧ ∀ N : Subgroup G, H ≤ N → N = ⊤ ∨ N = H) ↔ (∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ H = Subgroup.closure ({x ^ (n / p)} : Set G)) := sorry
