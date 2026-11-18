import Mathlib

open scoped BigOperators

theorem dummy {G : Type*} [Group G] (H : Subgroup G) (n : ℕ) (hn0 : 0 < n) (hG : Fintype G) (hH : Fintype H) (h : Fintype.card G = Fintype.card H * n) : ∃ K : Subgroup G, K.index = n + 1 := sorry
