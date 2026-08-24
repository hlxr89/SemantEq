import Mathlib
theorem c (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : Continuous f) (hfa : f a < 0) (hfb : 0 < f b) : ∃ c ∈ Set.Icc a b, f c = 0 := by sorry