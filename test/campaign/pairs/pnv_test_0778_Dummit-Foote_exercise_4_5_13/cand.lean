import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {n : ℕ} [Fintype G] (hn : Fintype.card G = n) (h : 56 ∣ n) : ∃ (p : ℕ) (hp : p.Prime) (H : Sylow p G), H.Normal := sorry
