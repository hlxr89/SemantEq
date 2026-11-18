import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) (hP : (P : Subgroup G).Normal) (H : Subgroup G) : ∃! Q : Sylow p H, (Q : Subgroup H) = Subgroup.comap H.subtype (P : Subgroup G) := sorry
