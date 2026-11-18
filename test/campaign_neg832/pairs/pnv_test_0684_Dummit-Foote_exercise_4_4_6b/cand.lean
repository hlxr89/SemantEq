import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (G : Type*) [Group G] (hG : ∃ H : Subgroup G, H.Normal ∧ ¬ H.Characteristic) : ∃ H : Subgroup G, H.Normal ∧ ¬ H.Characteristic := sorry
