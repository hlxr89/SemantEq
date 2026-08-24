/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Rudin.exercise_4_19  (source: Rudin)
-/
import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators
noncomputable section


/- ALT (C): witness location `a < x ∧ x < b` bundled as the bounded-exists membership `∃ x ∈ Set.Ioo a b` -/
theorem exercise_4_19_alt
  {f : ℝ → ℝ} (hf : ∀ a b c, a < b → f a < c → c < f b → ∃ x ∈ Set.Ioo a b, f x = c)
  (hg : ∀ r : ℚ, IsClosed {x | f x = r}) : Continuous f :=
sorry
