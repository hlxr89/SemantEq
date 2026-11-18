import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble has local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] (S : Set X) : (IsOpen S ∧ IsClosed S) ↔ IsClopen S := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_32a (A : Set ℕ) : IsClopen A := by
  exact isClopen_discrete A
