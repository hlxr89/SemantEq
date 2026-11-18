import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G H : Type*} [Group G] [Group H] {N : Subgroup G} {f : G →* H} (hf : Function.Surjective f) (h : N.Normal) : (N.map f).Normal := sorry
