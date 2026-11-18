import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_open : ∀ U : Set ℝ, IsOpen U → IsOpen (f '' U)) : ∃ (a b : ℝ), a < b ∧ ∀ x y : ℝ, x < y → f x ≤ f y ∨ f y ≤ f x := sorry
