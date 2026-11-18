import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type u} [Field F] {m : ℕ} [hFchar : CharP F p] (hm : p^n = m) (x : F) (hx : x^m = x) : x = 0 := sorry
