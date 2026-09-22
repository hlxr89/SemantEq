import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : UniformContinuous f) {x_n : ℕ → X} (hx : CauchySeq x_n) : CauchySeq (f ∘ x_n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_11a
  {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y]
  (f : X → Y) (hf : UniformContinuous f)
  (x : ℕ → X) (hx : CauchySeq x) :
  CauchySeq (λ n => f (x n)) := by
  simpa only [Function.comp_apply] using dummy_assumed hf hx
