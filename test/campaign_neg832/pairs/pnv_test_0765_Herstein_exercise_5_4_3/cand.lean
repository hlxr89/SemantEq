import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {K : Type*} [Field K] (p : K[X]) (a : K) (h : p.eval a = 0) : (minpoly K a).degree ≤ natDegree p := sorry
