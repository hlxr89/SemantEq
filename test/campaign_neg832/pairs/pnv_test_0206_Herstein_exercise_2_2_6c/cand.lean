import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (n : ℕ) [h0 : NeZero n] (a : G) (b : G) (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) : Commute a b := sorry
