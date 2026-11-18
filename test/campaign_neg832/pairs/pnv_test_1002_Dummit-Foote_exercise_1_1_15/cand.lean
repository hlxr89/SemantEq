import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] : ∀ (l : List G), (List.prod l)⁻¹ = (List.map (fun x => x⁻¹) l).prod := sorry
