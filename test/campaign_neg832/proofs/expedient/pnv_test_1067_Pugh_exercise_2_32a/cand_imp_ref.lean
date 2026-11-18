import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] (f : ℕ → X) : IsClopen (Set.range f) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_32a (A : Set ℕ) : IsClopen A := by
  exact isClopen_discrete A
