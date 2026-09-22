import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {A B : Type*} [Group A] [Group B] : Nonempty (A × B ≃* B × A) := sorry
