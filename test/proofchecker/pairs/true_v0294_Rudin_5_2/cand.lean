import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ioo a b)) (hder : ∀ x ∈ Set.Ioo a b, 0 < deriv f x) : StrictMonoOn f (Set.Ioo a b) ∧ DifferentiableOn ℝ (Inv.inv f) (f '' Set.Ioo a b) ∧ ∀ x ∈ Set.Ioo a b, deriv (Inv.inv f) (f x) = (deriv f x)⁻¹ := sorry
