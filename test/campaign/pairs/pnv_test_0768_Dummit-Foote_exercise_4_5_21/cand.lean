import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (G : Type*) [Group G] [h : Fintype G] (hG : Fintype.card G = 2907) : ¬IsSimpleGroup G := sorry
