import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) : UniformContinuousOn f (Set.Icc a b) ↔ ∀ ε > 0, ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x y⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → |x - y| < δ → |f x - f y| < ε := sorry
