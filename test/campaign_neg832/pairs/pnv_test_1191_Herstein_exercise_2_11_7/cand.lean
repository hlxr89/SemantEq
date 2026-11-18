import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type u} [Group G] (P : Sylow p G) : Function.Injective (Subtype.val : P → G) := sorry
