import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_open : ∀ U : Set ℝ, IsOpen U → IsOpen (f '' U)) : Monotone f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15 {f : ℝ → ℝ}
  (hf : Continuous f) (hof : IsOpenMap f) :
  Monotone f := by
  exact dummy_assumed hf hof
