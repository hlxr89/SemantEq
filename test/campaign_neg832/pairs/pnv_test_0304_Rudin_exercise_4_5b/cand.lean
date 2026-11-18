import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (h : ∀ x : ℝ, ∃ ε > 0, ∀ y, |y - x| < ε → f y ≠ x) : ∃ (E : Set ℝ)(hEmeas : MeasurableSet E) (hEne : Eᶜ.Nonempty)(hE : ∀ y ∈ E, ContinuousWithinAt f (Eᶜ) y), ¬∃ (g : ℝ → ℝ)(hgc : Continuous g), ∀ z ∈ E, g z = f z := sorry
