import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {g : ℝ → ℝ} (M : ℝ) (hg : ∀ x, |deriv g x| ≤ M) (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ) (hf : ∀ x, f x = x + ε * g x) : ∃ δ > 0, ε < δ → Function.Injective f := sorry
