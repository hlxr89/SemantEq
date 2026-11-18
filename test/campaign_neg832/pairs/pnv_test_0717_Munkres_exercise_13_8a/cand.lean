import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy (x : ℝ) : ∃ (a b : ℕ), b > a ∧ ∀ (A : Set ℝ), IsOpen A ∧ x ∈ A ↔ (∃ (n : ℕ), (a : ℝ) ≤ n ∧ n < b ∧ (n : ℝ) ∈ A) := sorry
