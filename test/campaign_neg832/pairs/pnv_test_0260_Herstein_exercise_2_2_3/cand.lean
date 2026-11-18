import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (G : Type*) [Group G] (a b : G) (ha : a ^ 2 = a) (hb : b ^ 2 = b) (hc : a ^ 3 * b ^ 3 = a ^ 3 * b): a = b := sorry
