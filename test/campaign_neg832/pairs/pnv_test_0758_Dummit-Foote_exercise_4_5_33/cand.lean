import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type u} [Group G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} (hP : P.Normal) (H : Subgroup G) : ∃! Q : Sylow p H, ∀ Q' : Sylow p H, Q ≤ Q' → Q = Q' := sorry
