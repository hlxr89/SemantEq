import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {p : ℕ} {α : ℕ} [hp : Fact p.Prime] (hG : Fintype.card G = p ^ α) (hα : α ≠ 0) : ∀ H : Subgroup G, Subgroup.index H = p → Normal H := sorry
